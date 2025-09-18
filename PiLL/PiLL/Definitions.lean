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

def mergeEnv (Δ Γ : Env) : Env :=
  Δ ∪ Γ

noncomputable def envLookupTypeOf (Δ : Env) (x : NonEmptyName) : Option Types :=
  (Δ.toList.find? (fun p => p.1 = x)).map Prod.snd

-- Order independent equality for environments
def envEq (Δ Γ : Env) : Prop :=
  ∀ x : (NonEmptyName), envLookupTypeOf Δ x = envLookupTypeOf Γ x
  -- Δ = Γ -- could work for finsets but breaks all the other envEq proofs

-- Eq reflexivity
theorem envEqRefl (Δ : Env) : envEq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
theorem envEqSymm (Δ Γ : Env) (h : envEq Δ Γ) : envEq Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
theorem envEqTrans (Δ Γ Ε : Env) (h₁ : envEq Δ Γ) (h₂ : envEq Γ Ε) : envEq Δ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

-- identity
theorem mergeEnvUnitRight (Δ : Env) : mergeEnv Δ EmptyEnv = some Δ := by
  simp [mergeEnv]

-- commutivity
theorem mergeEnvComm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Δ Γ:= by
  simp

-- associativity
theorem mergeEnvAssoc (Δ Γ Ε : Env) : mergeEnv (mergeEnv Δ Γ) Ε = mergeEnv Δ (mergeEnv Γ Ε) := by
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
  hyperEnvLinearity 𝒢 ∧ hyperEnvLinearity ℋ ∧
  ((𝒢.map Prod.fst).toFinset ∩ (ℋ.map Prod.fst).toFinset).card = 0 ∧
  ∀ x : NonEmptyName, ¬ (𝒢(x) ≠ none ∧ ℋ(x) ≠ none)

noncomputable def mergeHyperEnv (𝒢 ℋ : HyperEnv) : Option HyperEnv :=
 if disjointHyperEnv 𝒢 ℋ = true then some (𝒢 ++ ℋ) else none

def hyperLookup (𝒢 : HyperEnv) (Δ : EnvNames) : Option Env :=
  (𝒢.find? (fun p => p.fst = Δ)).map Prod.snd

def hyperEnvNames (𝒢 : HyperEnv) : Finset (NonEmptyName) :=
  𝒢.foldl (fun acc ⟨_, Δ⟩ => acc ∪ Δ.image Prod.fst) ∅ -- ∅ is the initial set

-- Order independent equality for hyper-environments
def hyperEnvEq (𝒢 ℋ : HyperEnv) : Prop :=
  ∀ x ∈ hyperEnvNames 𝒢 ∪ hyperEnvNames ℋ,
    𝒢(x) = ℋ(x)

-- reflexivity
theorem hyperEnvEq.relf (𝒢 : HyperEnv) : hyperEnvEq 𝒢 𝒢 := by
  simp [hyperEnvEq]

-- symmetry
theorem hyperEnvEq.symm (𝒢 ℋ : HyperEnv) (h : hyperEnvEq 𝒢 ℋ) : hyperEnvEq ℋ 𝒢 := by
  intro x hx
  apply Eq.symm
  apply h
  rw [Finset.union_comm]
  exact hx

-- transitivity
theorem hyperEnvEq.trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : hyperEnvEq 𝒢 ℋ) (h₂ : hyperEnvEq ℋ 𝒦) :
  hyperEnvEq 𝒢 𝒦 := by sorry



-- add proofs for
  -- associativity
  -- commutivity
  -- identity









------------------------------------------ TODOs  ------------------------------------------
-- TODO: Check equality on hypersets are across env names as well as names within those envs

-- TODO: define prettier merge notation more like in the article
  --  Γ,• = Γ     Γ,Δ = Δ,Γ       (Γ,Δ),Ξ = Γ,(Δ,Ξ)       (maybe don't use ',')
  -- G|∅ = G      G|H = H|G       (G|H)|I = G|(H|I)       (maybe use '|ₕ')

-- make notation for:
  -- creating a hyper-environment when doing parallel composition of multiple environments

-- TODO: Prove associativity, commutativity, identity for hyper-/environments

-- TODO: Define dual operator s.t:
  -- (𝐴 ⊗ 𝐵)^⊥ = 𝐴^⊥ ⅋ 𝐵^⊥
  -- (𝐴 ⅋ 𝐵)^⊥ = 𝐴^⊥ ⊗ 𝐵^⊥
  -- 1^⊥ = ⊥
  -- ⊥^⊥ = 1

-- TODO: Define name function returning the names in a hyper-/environment???

-- TODO: define typing rules with side condition enforcing
  -- Environments can only contain one occurence of a process name
  -- Hyper-environments can only contain one occurence of an environment name
  -- i.e. typing rules should enforce linearity

-- TODO: define wellformedness for hyper-environments

-- TODO: make a smart constructor for hyper-environments for less boiler plate?


------------ Questions ------------
-- Is it the typing rules which ensure that a single name cannot be used by multiple environments
-- Otherwise how is 𝒢(x) supposed to be defined
-- Is it correctly understood that typing rules ensure name linearity in environments


------------ Might be irrelevant ------------
-- TODO: use env_linearity to ensure insertions / appends to an env's data are unique entries
-- TODO: use hyper_linearity to ensure insertions / appends to an hyperenv's data are unique entries


------------------------------------------ DONE ------------------------------------------
-- TODO: make environments and hyper-environments ignore the order of their elements


----------------------------------------- NOTES -----------------------------------------
-- Linearity on hypersets should be enforced through typing rules and should make it impossible
-- to define multiple instances of the same name across different environments s.t. 𝒢(x) is un-
-- ambigous.
