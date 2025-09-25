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
  restriction : Bool := val ≠ " " && val.all Char.isUpper || val = "∅" -- FIXME: Make prop??
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
  | tensor : Types → Types → Types        -- t₁ ⊗ t₂ (send)
  | parr : Types → Types → Types     -- t₁ ⅋ t₂ (receive)
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

def envFromPair (x : NonEmptyName) (A : Types) : Env :=
  { (x, A) }

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
      hyperLookupTypeOf 𝒢 x = hyperLookupTypeOf ℋ x := h₁_vals x hx
      _    = hyperLookupTypeOf 𝒦 x := h₂_vals x hxH

instance : Equivalence hyperEnvEq :=
⟨hyperEnvEq.refl, @hyperEnvEq.symm, @hyperEnvEq.trans⟩

noncomputable def mergeHyperEnv (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

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

----------------------------------------- NOTATION -----------------------------------------
/- PROC -/
notation:60 x "[" y "]" "." P => Proc.tensor x y P
notation:60 x "(" y ")" "." P => Proc.parr x y P
notation:60 x "[" "]" "." P => Proc.one x P
notation:60 x "(" ")" "." P => Proc.bot x P
notation:60 "𝓋" "(" x ", " y ") " P => Proc.cut x y P
infixr:55 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil

/- TYPING -/
notation:60 A " ⊗ " B => Types.tensor A B
notation:60 A " ⅋ " B => Types.parr A B
notation "𝟙" => Types.one
notation "⊥" => Types.bot
notation:max "¬" A => neg A

/- ENV -/
syntax envItem := term          -- existing env or binding
syntax envBind := term " : " term
syntax envList := sepBy1((envItem <|> envBind), ", ")
syntax envExpr := envList

-- -----------------------------
-- Macro to fold comma chains
-- -----------------------------
open Lean Macro in
macro_rules
  | `($x:term : $A:term) => `(envFromPair $x $A)
  | `($xs:envList) => do
    let mut result ←
      match xs.elems[0] with
      | `( $x:term : $A:term ) => `(envFromPair $x $A)
      | stx                     => pure stx
    for i in [1:xs.elems.size] do
      let stx := xs.elems[i]
      let env ← match stx with
        | `( $x:term : $A:term ) => `(envFromPair $x $A)
        | other                  => pure other
      result ← `(mergeEnv $result $env)
    return result

variable (Δ : Env) (x y : NonEmptyName) (A B : Types)



/- HYPERENV -/
notation 𝒢 "(" x ")" => hyperLookupTypeOf 𝒢 x
notation 𝒢:60 " |ₕ " ℋ => mergeHyperEnv 𝒢 ℋ


--------------------------------------- TYPING RULES ---------------------------------------

-- Notation:
  -- x[y].P             => send y on x and continue as P
  -- x[].P              => send empty message on x and continue as P
  -- x(y).P             => receive y on x and continue as P
  -- x().P              => receive empty message on x and continue as P
  -- 𝓋(x, y) P          => name restriction or cut open comm channel x-y
  -- P |ₚ Q              => Parallel composition of process P and Q
  -- 𝟘                  => The terminated process
  -- ∅                  => Empty env / hyperenv depending on context
  -- A ⊗ B             => send A and continue as B
  -- A ⅋ B             => receive A and continue as B
  -- x : A              => the name x typed with A
  -- 𝟙                  => empty output unit for send (⊗)
  -- ⊥                  => empty output unit for receive (⅋)
  -- ¬                  => logical negation as well as atom negation (duality)
  -- 𝒢(x)               => returns the typing of x in 𝒢
  -- ℋ |ₕ 𝒢 = 𝒢 |ₕ ℋ    => parallel composition of hyperenvs
  -- Δ |ₕ Γ             => parallel composition of envs => hyperenv (coercions of env ↑ HyperEnv)
  -- Δ |ₑ Γ             => merging Δ and Γ into a single env
  -- x : A              => creates the singleton environment {(x, A)} where x is typed with a


variable (𝒢 ℋ 𝒦 : HyperEnv) (Δ Γ Ε : Env) (P Q : Proc)
  (x y : NonEmptyName) (A B : Types)

-- inductive Typing : HyperEnv → Proc → Prop where
--   | mix₀    : Typing ∅ 𝟘
--   | mix     : Typing 𝒢 P → Typing ℋ Q → Typing (𝒢 |ₕ ℋ) (P |ₚ Q)
--   | cut     : Typing (𝒢 |ₕ (Γ |ₑ x : A) |ₕ (Δ |ₑ y : ¬A)) P → Typing (𝒢 |ₕ Γ |ₕ Δ) (𝓋(x, y) P)
--   | tensor    : Typing ((Γ |ₑ y : A) |ₕ (Δ |ₑ x : B)) P → Typing (Γ |ₑ Δ |ₑ x : (A ⊗ B)) (x[y].P)
--   | one     : Typing ∅ P → Typing (x : 𝟙) (x[].P)
--   | parr : Typing (Γ |ₑ (y : A) |ₑ (x : B)) P → Typing (Γ |ₑ x : (A ⅋ B)) P
--   | bot     : Typing Γ P → Typing (Γ |ₑ x : ⊥) (x().P)


inductive πLL : Type where
  | sorry




    -- "⊢" Proc.nil "∷" ∅





------------------------------------------ TODOs  ------------------------------------------



-- TODO: Fix |ₕ binding tighter than |ₑ and :

-- TODO: Fix "¬" usage as dual operator and define "⫠" postfix or some other operator

-- TODO: get comma operator to work as in the paper instead of |ₑ

-- TODO: replace finset with AList and make canonical form to create commutivity, associativity, ...

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

-- In the cut rule for πMLL is the typing correct i.e. 𝒢 | Γ, x : A | Δ, y : ¬A becomes 𝒢 | Γ, Δ
  -- i.e. is it correct that after the cut Γ and Δ merges into one environment?
  -- Or should they stay parallel when merging into 𝒢 again?




------------ Might be irrelevant ------------
-- TODO: use env_linearity to ensure insertions / appends to an env's data are unique entries
-- TODO: use hyper_linearity to ensure insertions / appends to an hyperenv's data are unique entries


----------------------------------------- NOTES -----------------------------------------
-- Linearity on hypersets should be enforced through typing rules and should make it impossible
-- to define multiple instances of the same name across different environments s.t. 𝒢(x) is un-
-- ambigous.
