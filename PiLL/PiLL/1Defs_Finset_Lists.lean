----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
------------------------------------------ Proc  ------------------------------------------

abbrev Name := String

structure NonEmptyName where
  (val : String)
  (ne_empty : val ≠ " ")
deriving Repr, BEq, DecidableEq

inductive Proc where
  | send : NonEmptyName → Name → Proc → Proc     -- x[y].P ∧ x[].P (output y on x and continue as P)
  | receive : NonEmptyName → Name → Proc → Proc  -- x(y).P ∧ x().P (input y on x and continue as P)
  | cut : NonEmptyName → NonEmptyName → Proc     -- vxy P          (name restriction, or "cut")
  | par : Proc → Proc → Proc                     -- parallel composition of two processes
  | nil : Proc                                   -- terminated process
deriving Repr

notation:60 x "[" y "]" "." P => Proc.send x y P
notation:60 x "(" y ")" "." P => Proc.receive x y P
notation:60 "v" x y P => Proc.cut x y P
infixr:55 " ∣ " => Proc.par -- normal pipe creates issues with lean's matching so this is \mid
notation "𝟘" => Proc.nil

------------------------------------------ TYPES  ------------------------------------------

structure NonEmptyTypes where
  (val : String)
  (restriction : val ≠ " " ∧ val.all Char.isUpper ∨ val = "∅")
deriving Repr, BEq, DecidableEq

inductive Types where
  | term : NonEmptyTypes → Types        -- named type, like A, B, ...
  | send : Types → Types → Types        -- send arg₁ continue as arg₂
  | receive : Types → Types → Types     -- receive arg₁ continue as arg₂
  | one : Types                         -- 1 (empty output, unit for ⊗)
  | bot : Types                         -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

notation:60 A " ⊗ " B => Types.send A B
notation:60 A " ⅋ " B => Types.receive A B
notation "𝟙" => Types.one
notation "⊥" => Types.bot

--------------------------------------- ENVIRONMENTS ---------------------------------------

def upperCaseGreekLetters : List (Char) :=
  ['Α', 'Β', 'Γ', 'Δ', 'Ε', 'Ζ', 'Η', 'Θ', 'Ι', 'Κ', 'Λ', 'Μ',
  'Ν', 'Ξ', 'Ο', 'Π', 'Ρ', 'Σ', 'Τ', 'Υ', 'Φ', 'Χ', 'Ψ', 'Ω']

structure EnvNames where -- Do I need to derive the Eq things
  (val : { s : String // s ≠ " " ∧ s.all (· ∈ upperCaseGreekLetters) })
deriving Repr, BEq, DecidableEq

abbrev Env := Finset (NonEmptyName × Types)

def joinWithSep (elems) (sep) :=
  match elems with
  | []      => ""
  | [x]     => x
  | x :: xs => xs.foldl (fun acc y => acc ++ sep ++ y) x

abbrev EmptyEnv : Env := {}

def envLinearity (Δ : Env) : Prop :=
  (Δ.image Prod.fst).card = Δ.card

def disjointEnv (Δ Γ : Env) : Prop :=
  (Δ.image Prod.fst ∩ Γ.image Prod.fst).card = 0

noncomputable def envLookupTypeOf (Δ : Env) (x : NonEmptyName) : Option Types :=
  (Δ.toList.find? (fun p => p.1 = x)).map Prod.snd

-- Order independent equality for environments
def envEq (Δ Γ : Env) : Prop :=
  ∀ x : (NonEmptyName), envLookupTypeOf Δ x = envLookupTypeOf Γ x
  -- Δ = Γ -- could work for finsets but breaks all the other envEq proofs

-- Eq reflexivity
theorem envEq.refl (Δ : Env) : envEq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
theorem envEq.symm (Δ Γ : Env) (h : envEq Δ Γ) : envEq Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
theorem envEq.trans (Δ Γ Ε : Env) (h₁ : envEq Δ Γ) (h₂ : envEq Γ Ε) : envEq Δ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence envEq :=
⟨envEq.refl, @envEq.symm, @envEq.trans⟩

def mergeEnv (Δ Γ : Env) : Env := Δ ∪ Γ

-- identity
theorem mergeEnv.unitR (Δ : Env) : mergeEnv Δ EmptyEnv = Δ := by
  simp [mergeEnv]

theorem mergeEnv.unitL (Δ : Env) : mergeEnv EmptyEnv Δ = Δ := by
  simp [mergeEnv]

-- commutivity
theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Δ Γ:= by
  simp

-- associativity
theorem mergeEnv.assoc (Δ Γ Ε : Env) : mergeEnv (mergeEnv Δ Γ) Ε = mergeEnv Δ (mergeEnv Γ Ε) := by
  simp [mergeEnv]

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := List (EnvNames × Env)

abbrev EmptyHyperEnv : HyperEnv := []

def pairwise {α : Type} (r : α → α → Prop) : List α → Prop
| [] => True
| (x :: xs) => (∀ y ∈ xs, r x y) ∧ pairwise r xs

def hyperEnvLinearity (𝒢 : HyperEnv) : Prop :=
  (𝒢.map Prod.fst).toFinset.card = 𝒢.length ∧          -- ensure distinct env names
  ∀ Δ ∈ 𝒢, envLinearity Δ.snd ∧                        -- ensure each env is linear
  pairwise (fun e1 e2 => disjointEnv e1.snd e2.snd) 𝒢  -- ensure pairwise env disjointness

def hyperEnvNames (𝒢 : HyperEnv) : Finset (NonEmptyName) :=
  𝒢.foldl (fun acc ⟨_, Δ⟩ => acc ∪ Δ.image Prod.fst) ∅ -- ∅ is the initial set

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def hyperLookupTypeOf (𝒢 : HyperEnv) (x : NonEmptyName) : Option Types :=
  (𝒢.findSome? (fun Δ => envLookupTypeOf Δ.snd x))

notation 𝒢 "(" x ")" => hyperLookupTypeOf 𝒢 x

def disjointHyperEnv (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  hyperEnvLinearity 𝒢 ∧ hyperEnvLinearity ℋ ∧
  ((𝒢.map Prod.fst).toFinset ∩ (ℋ.map Prod.fst).toFinset).card = 0 ∧
  (hyperEnvNames 𝒢 ∩ hyperEnvNames ℋ) = ∅

def hyperLookup (𝒢 : HyperEnv) (Δ : EnvNames) : Option Env :=
  (𝒢.find? (fun p => p.fst = Δ)).map Prod.snd

-- Order independent equality for hyper-environments
def hyperEnvEq (𝒢 ℋ : HyperEnv) : Prop :=
  hyperEnvNames 𝒢 = hyperEnvNames ℋ ∧ -- all names defined must match across the hyperenvs
  ∀ x ∈ hyperEnvNames 𝒢, 𝒢(x) = ℋ(x)  -- ∀ the defined names their types must be the same

-- reflexivity
theorem hyperEnvEq.refl (𝒢 : HyperEnv) : hyperEnvEq 𝒢 𝒢 := by
  simp [hyperEnvEq]

-- symmetry
theorem hyperEnvEq.symm (𝒢 ℋ : HyperEnv) (h : hyperEnvEq 𝒢 ℋ) : hyperEnvEq ℋ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- transitivity
theorem hyperEnvEq.trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : hyperEnvEq 𝒢 ℋ) (h₂ : hyperEnvEq ℋ 𝒦) :
  hyperEnvEq 𝒢 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ hyperEnvNames ℋ := by rw [← h₁_names]; exact hx
    calc
      𝒢(x) = ℋ(x) := h₁_vals x hx
      _    = 𝒦(x) := h₂_vals x hxH

instance : Equivalence hyperEnvEq :=
⟨hyperEnvEq.refl, @hyperEnvEq.symm, @hyperEnvEq.trans⟩

noncomputable def mergeHyperEnv (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ++ ℋ

-- identity
theorem mergeHyperEnv.unitL (𝒢 : HyperEnv) : mergeHyperEnv EmptyHyperEnv 𝒢 = 𝒢 := by
  simp [mergeHyperEnv]

theorem mergeHyperEnv.unitR (𝒢 : HyperEnv) : mergeHyperEnv 𝒢 EmptyHyperEnv = 𝒢 := by
  simp [mergeHyperEnv]

theorem mergeHyperEnv.comm (𝒢 ℋ : HyperEnv) : mergeHyperEnv 𝒢 ℋ = mergeHyperEnv ℋ 𝒢 := by
simp [mergeHyperEnv]
sorry

-- associativity
theorem mergeHyperEnv.assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  mergeHyperEnv (mergeHyperEnv 𝒢 ℋ) 𝒦 = mergeHyperEnv 𝒢 (mergeHyperEnv ℋ 𝒦) := by
  simp [mergeHyperEnv]
