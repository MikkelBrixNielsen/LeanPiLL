----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
------------------------------------------ Proc  ------------------------------------------

abbrev Name := String

-- structure NonEmptyName where
--   (val : String)
--   (ne_empty : val ≠ " ")
-- deriving Repr, BEq, DecidableEq

-- structure EmptyName where
--   (val : String)
--   (is_empty : val = "")
-- deriving Repr, BEq, DecidableEq

-- inductive Proc : Type where
--   | send : NonEmptyName → NonEmptyName → Proc → Proc  -- x[y].P (output y on x and continue as P)
--   | sendₑ : NonEmptyName → EmptyName → Proc → Proc  -- x[].P
--   | receive : NonEmptyName → NonEmptyName → Proc → Proc -- x(y).P (input y on x and continue as P)
--   | receiveₑ : NonEmptyName → EmptyName → Proc → Proc -- x().P
--   | cut : NonEmptyName → NonEmptyName → Proc → Proc -- vxy P (name restriction, or "cut")
--   | par : Proc → Proc → Proc  -- parallel composition of two processes
--   | nil                                          -- terminated process
-- deriving Repr

inductive Payload where
  | empty  : Payload
  | named  : (val : String) → (h : val ≠ "") → Payload
deriving Repr, BEq, DecidableEq

inductive Proc : Type where
  | send : NonEmptyName → Payload → Proc → Proc  -- x[y].P (output y on x and continue as P)
  | receive : NonEmptyName → Payload → Proc → Proc -- x(y).P (input y on x and continue as P)
  | cut : NonEmptyName → Payload → Proc → Proc -- vxy P (name restriction, or "cut")
  | par : Proc → Proc → Proc  -- parallel composition of two processes
  | nil                                          -- terminated process
deriving Repr

notation:60 x "[" y "]" "." P => Proc.send x y P
notation:60 x "(" y ")" "." P => Proc.receive x y P
notation:60 "𝓋 " x y P => Proc.cut x y P
infixr:55 " |ₚ " => Proc.par -- normal pipe creates issues with lean's matching
notation "𝟘" => Proc.nil

------------------------------------------ TYPES  ------------------------------------------

structure NonEmptyTypes where
  val : String
  restriction : Bool := val ≠ " " && val.all Char.isUpper || val = "∅" -- FIXME: Make prop
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
  | send : Types → Types → Types        -- t₁ ⊗ t₂ (send)
  | receive : Types → Types → Types     -- t₁ ⅋ t₂ (receive)
  | one : Types                         -- 𝟙 (empty output, unit for ⊗)
  | bot : Types                         -- ⊥ (empty send, unit for ⅋)
deriving Repr, BEq, DecidableEq

notation:60 A " ⊗ " B => Types.send A B
notation:60 A " ⅋ " B => Types.receive A B
notation "𝟙" => Types.one
notation "⊥" => Types.bot

def neg : Types → Types
| A ⅋ B => (neg A) ⊗ (neg B)
| A ⊗ B => (neg A) ⅋ (neg B)
| 𝟙 => ⊥
| ⊥ => 𝟙
| Types.term T => Types.term T.neg

notation:max "¬" A => neg A  -- FIXME: check if this conflicts with Lean's standard negator

--------------------------------------- ENVIRONMENTS ---------------------------------------

def upperCaseGreekLetters : List (Char) :=
  ['Α', 'Β', 'Γ', 'Δ', 'Ε', 'Ζ', 'Η', 'Θ', 'Ι', 'Κ', 'Λ', 'Μ',
  'Ν', 'Ξ', 'Ο', 'Π', 'Ρ', 'Σ', 'Τ', 'Υ', 'Φ', 'Χ', 'Ψ', 'Ω']

structure EnvNames where -- Do I need to derive the Eq things
  (val : { s : String // s ≠ " " ∧ s.all (· ∈ upperCaseGreekLetters) })
deriving Repr, BEq, DecidableEq

abbrev Env := Finset (NonEmptyName × Types)

abbrev EmptyEnv : Env := {}

def extendEnv (Δ : Env) (x : NonEmptyName) (A : Types) : Env :=
  Δ ∪ { (x, A) }

notation Δ " |ₓ " x " : " A => extendEnv Δ x A -- TODO: FIXME make more pretty

def Env.mk : List (NonEmptyName × Types) → Env --  Env.mk [(x,A), (y,B)]
  | [] => EmptyEnv
  | (x, A) :: xs => extendEnv (Env.mk xs) x A

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

-- abbrev HyperEnv := Finset (EnvNames × Env)
abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := {}

def extendHyperEnv (𝒢 : HyperEnv) (Γ : Env) : HyperEnv :=
  𝒢 ∪ { Γ }

notation 𝒢 " |ₓ " Δ => extendHyperEnv 𝒢 Δ

def parEnv (Δ Γ : Env) : HyperEnv :=
  {Δ, Γ}

notation Δ " |ₑ " Γ => parEnv Δ Γ


def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def hyperEnvLinearity (𝒢 : HyperEnv) : Prop :=
  -- (𝒢.image Prod.fst).card = 𝒢.card ∧                  -- ensure distinct env name
  -- ∀ Δ ∈ 𝒢, envLinearity Δ.snd ∧                       -- ensure each env is linear
  -- pairwise (fun Δ Γ => disjointEnv Δ.snd Γ.snd) 𝒢     -- ensure pairwise env disjointness
  ∀ Δ ∈ 𝒢, envLinearity Δ ∧                              -- ensure each env is linear
  pairwise (fun Δ Γ => disjointEnv Δ Γ) 𝒢                -- ensure pairwise env disjointness

def getNamesInHyperEnv (𝒢 : HyperEnv) : Finset NonEmptyName :=
  -- Finset.fold (· ∪ ·) ∅ getNamesInEnv (𝒢.image Prod.snd)
  Finset.fold (· ∪ ·) ∅ getNamesInEnv 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def hyperLookupTypeOf (𝒢 : HyperEnv) (x : NonEmptyName) : Option Types :=
  -- (𝒢.toList.find? (fun Δ => envLookupTypeOf Δ.snd x ≠ none)) >>= fun Δ  => envLookupTypeOf Δ.snd x
  (𝒢.toList.find? (fun Δ => envLookupTypeOf Δ x ≠ none)) >>= fun Δ  => envLookupTypeOf Δ x

notation 𝒢 "(" x ")" => hyperLookupTypeOf 𝒢 x

def disjointHyperEnv (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  -- hyperEnvLinearity 𝒢 ∧ hyperEnvLinearity ℋ ∧
  -- ((𝒢.toList.map Prod.fst).toFinset ∩ (ℋ.toList.map Prod.fst).toFinset).card = 0 ∧
  -- (getNamesInHyperEnv 𝒢 ∩ getNamesInHyperEnv ℋ) = ∅
  hyperEnvLinearity 𝒢 ∧ hyperEnvLinearity ℋ ∧
  (𝒢 ∩ ℋ).card = 0 ∧
  (getNamesInHyperEnv 𝒢 ∩ getNamesInHyperEnv ℋ) = ∅

-- noncomputable def hyperLookup (𝒢 : HyperEnv) (Δ : EnvNames) : Option Env :=
--   (𝒢.toList.find? (fun p => p.fst = Δ)).map Prod.snd

-- Order independent equality for hyper-environments
def hyperEnvEq (𝒢 ℋ : HyperEnv) : Prop :=
  getNamesInHyperEnv 𝒢 = getNamesInHyperEnv ℋ ∧ -- all names defined must match across the hyperenvs
  ∀ x ∈ getNamesInHyperEnv 𝒢, 𝒢(x) = ℋ(x)  -- ∀ the defined names their types must be the same

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
    have hxH : x ∈ getNamesInHyperEnv ℋ := by rw [← h₁_names]; exact hx
    calc
      𝒢(x) = ℋ(x) := h₁_vals x hx
      _    = 𝒦(x) := h₂_vals x hxH

instance : Equivalence hyperEnvEq :=
⟨hyperEnvEq.refl, @hyperEnvEq.symm, @hyperEnvEq.trans⟩

noncomputable def mergeHyperEnv (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

notation 𝒢 " |ₕ " ℋ => mergeHyperEnv 𝒢 ℋ -- TOOD: FIXME make more pretty

-- identity
theorem mergeHyperEnv.unitL (𝒢 : HyperEnv) : mergeHyperEnv EmptyHyperEnv 𝒢 = 𝒢 := by
  simp [mergeHyperEnv]

theorem mergeHyperEnv.unitR (𝒢 : HyperEnv) : mergeHyperEnv 𝒢 EmptyHyperEnv = 𝒢 := by
  simp [mergeHyperEnv]

-- commutative
theorem mergeHyperEnv.comm (𝒢 ℋ : HyperEnv) : mergeHyperEnv 𝒢 ℋ = mergeHyperEnv ℋ 𝒢 := by
  simp [mergeHyperEnv, Finset.union_comm]

-- associativity
theorem mergeHyperEnv.assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  mergeHyperEnv (mergeHyperEnv 𝒢 ℋ) 𝒦 = mergeHyperEnv 𝒢 (mergeHyperEnv ℋ 𝒦) := by
  simp [mergeHyperEnv]

--------------------------------------- TYPING RULES ---------------------------------------

variable (𝒢 ℋ 𝒦 : HyperEnv) (Δ Γ Ε : Env) (P Q : Proc)
  (x y : NonEmptyName) (A B : Types)

inductive Typing : HyperEnv -> Proc -> Prop where
  | mix₀    : Typing ∅ 𝟘
  | mix     : Typing 𝒢 P → Typing ℋ Q -> Typing (𝒢 |ₕ ℋ) (P |ₚ Q)
  | cut     : Typing (𝒢 |ₕ (Γ |ₓ x : A) |ₑ (Δ |ₓ y : ¬A)) P -> Typing (𝒢 |ₕ (Γ |ₑ Δ)) (Proc.cut x y P)
  | send    : Typing ((Γ |ₓ y : A) |ₑ (Δ |ₓ x : B)) P -> Typing (Γ |ₑ Δ |ₓ x : (A ⊗ B)) (x[y].P)
  | receive : Typing
  | one     : Typing
  | bot     : Typing






inductive πLL : Type where
  | sorry




    -- "⊢" Proc.nil "∷" ∅





------------------------------------------ TODOs  ------------------------------------------
-- Test that what has been defined works as inteded
    -- hyper- / env composition
    -- other things ??


-- TODO: Define dual operator s.t:
  -- (𝐴 ⊗ 𝐵)^⊥ = 𝐴^⊥ ⅋ 𝐵^⊥
  -- (𝐴 ⅋ 𝐵)^⊥ = 𝐴^⊥ ⊗ 𝐵^⊥
  -- 1^⊥ = ⊥
  -- ⊥^⊥ = 1

-- TODO: Add sidecondition to mix typing rule

-- TODO: define typing rules with side condition enforcing
  -- Environments can only contain one occurence of a process name
  -- Hyper-environments can only contain one occurence of an environment name
  -- i.e. typing rules should enforce linearity

-- TODO: make pretty notation for typing rules

-- TODO: define πLL transition rules (LTS) using pretty notation

-- TODO: define wellformedness for hyper-environments

-- TODO: make a smart constructor for hyper-environments for less boiler plate?


------------ Questions ------------
-- Is it the typing rules which ensure that a single name cannot be used by multiple environments
-- Otherwise how is 𝒢(x) supposed to be defined
-- Is it correctly understood that typing rules ensure name linearity in environments

-- How should hyperenvs be defined
  -- just a bag of envs no structure
  -- par constructor to keep track of structure
  -- processes have a parallel composition keeping them distinct so shouldn't this also
  -- be the case for hyperenvironments




------------ Might be irrelevant ------------
-- TODO: use env_linearity to ensure insertions / appends to an env's data are unique entries
-- TODO: use hyper_linearity to ensure insertions / appends to an hyperenv's data are unique entries


----------------------------------------- NOTES -----------------------------------------
-- Linearity on hypersets should be enforced through typing rules and should make it impossible
-- to define multiple instances of the same name across different environments s.t. 𝒢(x) is un-
-- ambigous.
