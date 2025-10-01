----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
------------------------------------------ Proc  ------------------------------------------

abbrev Name := String

structure NonEmptyName where
  (val : String)
  (neEmpty : val ≠ "")                  -- val not empty
  (no_spaces : ¬ (val.any (· = ' ')))   -- no spaces in val
deriving Repr, BEq, DecidableEq

inductive Proc : Type where
  | tensor   : NonEmptyName → NonEmptyName → Proc → Proc -- x[y].P (output y on x and continue as P)
  | parr     : NonEmptyName → NonEmptyName → Proc → Proc -- x(y).P (input y on x and continue as P)
  | one      : NonEmptyName → Proc → Proc                -- x[].P
  | bot      : NonEmptyName → Proc → Proc                -- x(y).P
  | cut      : NonEmptyName → NonEmptyName → Proc → Proc -- 𝓋xy P (name restriction, or "cut")
  | par      : Proc → Proc → Proc                        -- parallel composition of two processes
  | nil      : Proc                                      -- terminated process
deriving Repr

------------------------------------------ TYPES  ------------------------------------------

structure NonEmptyTypes where
  val : String
  restriction : Bool := val ≠ " " && val.all Char.isUpper || val = "∅"
deriving Repr, BEq, DecidableEq

def NonEmptyTypes.mkAuto (s : String) : NonEmptyTypes :=
  { val := s }

structure Atom where
  (name : NonEmptyTypes)
  (negated : Bool)
deriving Repr, BEq, DecidableEq

def Atom.mkAuto (s : String) (negated : Bool) : Atom :=
  { name := NonEmptyTypes.mkAuto s, negated := negated }

def Atom.neg (a : Atom) : Atom :=
  { a with negated := !a.negated }

inductive Types : Type where
  | term : Atom → Types                 -- named type, like A, B, ...
  | tensor : Types → Types → Types      -- t₁ ⊗ t₂ (send)
  | parr : Types → Types → Types        -- t₁ ⅋ t₂ (receive)
  | one : Types                         -- 𝟙 (empty output, unit for ⊗)
  | bot : Types                         -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

def neg : Types → Types
| Types.tensor A B => Types.parr (neg A) (neg B)
| Types.parr A B => Types.tensor (neg A) (neg B)
| Types.one => Types.bot
| Types.bot => Types.one
| Types.term T => Types.term T.neg

--------------------------------------- ENVIRONMENTS ---------------------------------------

def upperCaseGreekLetters : List (Char) :=
  ['Α', 'Β', 'Γ', 'Δ', 'Ε', 'Ζ', 'Η', 'Θ', 'Ι', 'Κ', 'Λ', 'Μ',
  'Ν', 'Ξ', 'Ο', 'Π', 'Ρ', 'Σ', 'Τ', 'Υ', 'Φ', 'Χ', 'Ψ', 'Ω']

structure EnvNames where
  (val : { s : String // s ≠ " " ∧ s.all (· ∈ upperCaseGreekLetters) })
deriving Repr, BEq, DecidableEq

abbrev Env := Finset (NonEmptyName × Types)

abbrev EmptyEnv : Env := {}

def Env.mk (x : NonEmptyName) (A : Types) : Env :=
  {(x, A)}

def envLinearity (Δ : Env) : Prop :=
  (Δ.image Prod.fst).card = Δ.card

def getNamesInEnv (Δ : Env) : Finset (NonEmptyName) :=
  (Δ.image Prod.fst)

def disjointEnv (Δ Γ : Env) : Prop :=
  (Δ.image Prod.fst ∩ Γ.image Prod.fst).card = 0

noncomputable def envLookupTypeOf (Δ : Env) (x : NonEmptyName) : Option Types :=
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

-- Order independent equality for environments
def envEq (Δ Γ : Env) : Prop :=
  ∀ x : (NonEmptyName), envLookupTypeOf Δ x = envLookupTypeOf Γ x

-- Eq reflexivity
@[simp]
theorem envEq.refl (Δ : Env) : envEq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
@[simp]
theorem envEq.symm (Δ Γ : Env) (h : envEq Δ Γ) : envEq Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
@[simp]
theorem envEq.trans (Δ Γ Ε : Env) (h₁ : envEq Δ Γ) (h₂ : envEq Γ Ε) : envEq Δ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence envEq :=
⟨envEq.refl, @envEq.symm, @envEq.trans⟩

def mergeEnv (Δ Γ : Env) : Env := Δ ∪ Γ

-- identity
@[simp]
theorem mergeEnv.unitR (Δ : Env) : mergeEnv Δ EmptyEnv = Δ := by
  simp [mergeEnv]

@[simp]
theorem mergeEnv.unitL (Δ : Env) : mergeEnv EmptyEnv Δ = Δ := by
  simp [mergeEnv]

-- commutivity
-- theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Γ Δ := by
@[simp]
theorem mergeEnv.comm (Δ Γ : Env) : mergeEnv Δ Γ = mergeEnv Γ Δ := by
  simp [mergeEnv]
  simp [Finset.union_comm]

-- associativity
@[simp]
theorem mergeEnv.assoc (Δ Γ Ε : Env) : mergeEnv (mergeEnv Δ Γ) Ε = mergeEnv Δ (mergeEnv Γ Ε) := by
  simp [mergeEnv]

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := {}

-- Coercion makes extending a hyperenv with env and merging the same
-- and env1 |ₕ env2 => hyperenv due to envs being lifted to hyperenv
instance : Coe Env HyperEnv := ⟨fun Γ => {Γ}⟩

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def hyperEnvLinearity (𝒢 : HyperEnv) : Prop :=
  ∀ Δ ∈ 𝒢, envLinearity Δ ∧                              -- ensure each env is linear
  pairwise (fun Δ Γ => disjointEnv Δ Γ) 𝒢                -- ensure pairwise env disjointness

def getNamesInHyperEnv (𝒢 : HyperEnv) : Finset NonEmptyName :=
  Finset.fold (· ∪ ·) ∅ getNamesInEnv 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def hyperLookupTypeOf (𝒢 : HyperEnv) (x : NonEmptyName) : Option Types :=
  (𝒢.toList.find? (fun Δ => envLookupTypeOf Δ x ≠ none)) >>= fun Δ  => envLookupTypeOf Δ x

def disjointHyperEnv (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  hyperEnvLinearity 𝒢 ∧ hyperEnvLinearity ℋ ∧
  (𝒢 ∩ ℋ).card = 0 ∧
  (getNamesInHyperEnv 𝒢 ∩ getNamesInHyperEnv ℋ) = ∅

-- Order independent equality for hyper-environments
def hyperEnvEq (𝒢 ℋ : HyperEnv) : Prop :=
  -- 𝒢 and ℋ must define the same names
  getNamesInHyperEnv 𝒢 = getNamesInHyperEnv ℋ ∧
  -- The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  ∀ x ∈ getNamesInHyperEnv 𝒢, hyperLookupTypeOf 𝒢 x = hyperLookupTypeOf ℋ x

-- reflexivity
@[simp]
theorem hyperEnvEq.refl (𝒢 : HyperEnv) : hyperEnvEq 𝒢 𝒢 := by
  simp [hyperEnvEq]

-- symmetry
@[simp]
theorem hyperEnvEq.symm (𝒢 ℋ : HyperEnv) (h : hyperEnvEq 𝒢 ℋ) : hyperEnvEq ℋ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- transitivity
@[simp]
theorem hyperEnvEq.trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : hyperEnvEq 𝒢 ℋ) (h₂ : hyperEnvEq ℋ 𝒦) :
  hyperEnvEq 𝒢 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ getNamesInHyperEnv ℋ := by rw [← h₁_names]; exact hx
    calc
      hyperLookupTypeOf 𝒢 x = hyperLookupTypeOf ℋ x := h₁_vals x hx
      _    = hyperLookupTypeOf 𝒦 x := h₂_vals x hxH

instance : Equivalence hyperEnvEq :=
⟨hyperEnvEq.refl, @hyperEnvEq.symm, @hyperEnvEq.trans⟩

noncomputable def mergeHyperEnv (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

-- identity
@[simp]
theorem mergeHyperEnv.unitL (𝒢 : HyperEnv) : mergeHyperEnv EmptyHyperEnv 𝒢 = 𝒢 := by
  simp [mergeHyperEnv]

@[simp]
theorem mergeHyperEnv.unitR (𝒢 : HyperEnv) : mergeHyperEnv 𝒢 EmptyHyperEnv = 𝒢 := by
  simp [mergeHyperEnv]

-- commutative
@[simp]
theorem mergeHyperEnv.comm (𝒢 ℋ : HyperEnv) : mergeHyperEnv 𝒢 ℋ = mergeHyperEnv ℋ 𝒢 := by
  simp [mergeHyperEnv, Finset.union_comm]

-- associativity
@[simp]
theorem mergeHyperEnv.assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  mergeHyperEnv (mergeHyperEnv 𝒢 ℋ) 𝒦 = mergeHyperEnv 𝒢 (mergeHyperEnv ℋ 𝒦) := by
  simp [mergeHyperEnv]

----------------------------------------- NOTATION -----------------------------------------

/- PROC -/
notation:80 x "⟦" y "⟧" "." P:80 => Proc.tensor x y P
notation:80 x "⟦" "⟧" "." P:80 => Proc.one x P
notation:80 x "⸨" y "⸩" "." P:80 => Proc.parr x y P
notation:80 x "⸨" "⸩" "." P:80 => Proc.bot x P
notation:60 "𝑣" "⸨" x ", " y "⸩ " P => Proc.cut x y P
notation "𝟘" => Proc.nil
infixr:65 " |ₚ " => Proc.par

/- TYPING -/
infixr:95 " ⊗ " => Types.tensor
infixr:95 " ⅋ " => Types.parr
notation:100 "𝟙" => Types.one
notation:100 "⊥" => Types.bot
notation:max A "ᗮ" => neg A

/- ENV -/
infixr:90 " ∶ " => Env.mk
infixr:85 "‚ " => mergeEnv

/- HYPERENV -/
notation:60 𝒢 "⸨" x "⸩" => hyperLookupTypeOf 𝒢 x
infixr:55 " |ₕ " => mergeHyperEnv

--------------------------------------- TYPING RULES ---------------------------------------

inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
    ----------
    Typing ∅ 𝟘

  | mix (𝒢 ℋ : HyperEnv) (P Q : Proc) :
    Typing 𝒢 P → Typing ℋ Q →
    --------------------------
     Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : NonEmptyName) (A : Types) :
    Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
    ---------------------------------------
        Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor (Γ Δ : Env) (P : Proc) (x y : NonEmptyName) (A B : Types) :
    Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
    ---------------------------------
    Typing (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦y⟧.P)

  | one (P : Proc) (x : NonEmptyName) :
        Typing ∅ P →
    --------------------
    Typing (x ∶ 𝟙) (x⟦⟧.P)

  | parr (Γ : Env) (P : Proc) (x y : NonEmptyName) (A B : Types) :
     Typing (Γ‚ y ∶ A‚ x ∶ B) P →
    -----------------------------
    Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩.P)

  | bot (Γ : Env) (P : Proc) (x : NonEmptyName) :
          Typing Γ P →
    ------------------------
    Typing (Γ‚ x ∶ ⊥) (x⸨⸩.P)

notation:50 "⊢ " P " ∷ " T => Typing T P

variable (x y z : NonEmptyName)
set_option pp.notation false in -- disable pretty print
#check Proc.cut x y (Proc.par (Proc.one x 𝟘) (Proc.bot y (Proc.one z 𝟘)))
set_option pp.notation false in -- disable pretty print
#check 𝑣⸨x , y⸩ x⟦⟧.𝟘 |ₚ y⸨⸩.z⟦⟧.𝟘

example (x y z : NonEmptyName) : ⊢ 𝑣⸨x , y⸩ x⟦⟧.𝟘 |ₚ y⸨⸩.z⟦⟧.𝟘 ∷ ∅ |ₕ ∅ |ₕ z ∶ 𝟙 := by
  apply Typing.cut ∅ ∅ (z ∶ 𝟙) _ _ _ (𝟙)
  rw [mergeHyperEnv.unitL]
  apply Typing.mix
  · apply Typing.one
    exact Typing.mix₀
  · apply Typing.bot
    apply Typing.one
    exact Typing.mix₀

-- Latch_xyz example from main.pdf
-- TODO: Try and use simp more, try and omit giving explicit types to cut,
--       in general try minimizing things given to cut
example (x x₁ x₂ y y₁ y₂ z : NonEmptyName) :
  ⊢ 𝑣⸨x₁, x₂⸩ 𝑣⸨y₁, y₂⸩ x⸨⸩.x₁⟦⟧.𝟘 |ₚ y⸨⸩.y₁⟦⟧.𝟘 |ₚ x₂⸨⸩.y₂⸨⸩.z⟦⟧.𝟘 ∷
    x ∶ ⊥‚ y ∶ ⊥‚ z ∶ 𝟙 := by
  apply Typing.cut ∅ _ _ _ _ _ (𝟙)
  rw [mergeHyperEnv.unitL, mergeEnv.comm]
  conv => lhs ; rhs ; rhs ; rw [mergeEnv.assoc]
  apply Typing.cut _ _ _ _ _ _ (𝟙)
  apply Typing.mix
  · apply Typing.bot
    apply Typing.one
    exact Typing.mix₀
  · apply Typing.mix
    · rw [mergeEnv.comm]
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀
    · conv => lhs ; rhs ; rw [mergeEnv.comm, ←mergeEnv.assoc] ; lhs ; rw [mergeEnv.comm]
      apply Typing.bot
      apply Typing.bot
      apply Typing.one
      exact Typing.mix₀

-- inductive πLL : Type where
--   | sorry
