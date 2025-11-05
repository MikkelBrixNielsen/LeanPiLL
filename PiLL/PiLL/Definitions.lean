----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Lean.PrettyPrinter.Delaborator
------------------------------------------ Proc  ------------------------------------------

abbrev PName := Nat -- Process names are just numbers (ensures not empty)

inductive Proc : Type where
  | tensor  (x y : PName) (P : Proc)   -- x[y].P
  | parr    (x y : PName) (P : Proc)   -- x(y).P
  | one     (x : PName) (P : Proc)     -- x[].P
  | bot     (x : PName) (P : Proc)     -- x().P
  | cut     (x y : PName) (P : Proc)   -- 𝒗xy P
  | _par     (P Q : Proc)               -- P | Q
  | nil                                -- 𝟘
deriving DecidableEq

notation:80 x "⟦" y "⟧" "." P:80 => Proc.tensor x y P
notation:80 x "⟦⟧" "." P:80 => Proc.one x P
notation:80 x "⸨" y "⸩" "." P:80 => Proc.parr x y P
notation:80 x "⸨⸩" "." P:80 => Proc.bot x P
notation:60 "𝑣" "⸨" x ", " y "⸩ " P => Proc.cut x y P

notation "𝟘" => Proc.nil

-- Process parallel only happens when if both processes aren't 𝟘
@[simp]
def Proc.par : Proc → Proc → Proc
  | 𝟘, Q => Q
  | P, 𝟘 => P
  | P, Q =>  Proc._par P Q

infixr:65 " |ₚ " => Proc.par

private def reprProcAux : Proc → Nat → String
  | .nil, _ => "𝟘"
  | .tensor x y P, _ => s!"{x}⟦{y}⟧.{reprProcAux P 0}"
  | .one x P, _ => s!"{x}⟦⟧.{reprProcAux P 0}"
  | .parr x y P, _ => s!"{x}⸨{y}⸩.{reprProcAux P 0}"
  | .bot x P, _ => s!"{x}⸨⸩.{reprProcAux P 0}"
  | .cut x y P, _ => s!"𝑣⸨{x}, {y}⸩ {reprProcAux P 0}"
  | ._par P Q, _ => s!"({reprProcAux P 0} |ₚ {reprProcAux Q 0})"

instance : Repr Proc where
  reprPrec P _ := reprProcAux P 0

instance : ToString Proc where
  toString p := reprStr p

-- inductive ProcCongr : Proc → Proc → Prop
--   | refl (P : Proc) : ProcCongr P P
--   | symm (P Q : Proc) : ProcCongr P Q → ProcCongr Q P
--   | trans (P Q R : Proc) : ProcCongr P Q → ProcCongr Q R → ProcCongr P R
--   | par_nil_l (P : Proc) : ProcCongr (𝟘 |ₚ P) P
--   | par_nil_r (P : Proc) : ProcCongr (P |ₚ 𝟘) P
--   | par_comm (P Q : Proc) : ProcCongr  (P |ₚ Q) (Q |ₚ P)
--   | par_assoc (P Q R : Proc) : ProcCongr ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- notation:50 P " ≡ₚ " Q => ProcCongr P Q

-- @[simp]
-- theorem Proc.nil_par_eq_nil : 𝟘 |ₚ 𝟘 ≡ₚ 𝟘 := by
--   apply ProcCongr.par_nil_l

-- @[simp]
-- theorem Proc.par_nil (P : Proc) : P |ₚ 𝟘 ≡ₚ P := by
--   apply ProcCongr.par_nil_r

-- @[simp]
-- theorem Proc.nil_par (P : Proc) : 𝟘 |ₚ P ≡ₚ P := by
--   apply ProcCongr.par_nil_l

abbrev Renaming := PName → PName

def rename (ρ : Renaming) : Proc → Proc
  | .tensor x y P => .tensor (ρ x) (ρ y) (rename ρ P)
  | .parr x y P   => .parr (ρ x) (ρ y) (rename ρ P)
  | .one x P      => .one (ρ x) (rename ρ P)
  | .bot x P      => .bot (ρ x) (rename ρ P)
  | .cut x y P    => .cut (ρ x) (ρ y) (rename ρ P)
  | ._par P Q      => .par (rename ρ P) (rename ρ Q)
  | .nil          => .nil

@[simp]
def Proc.fNames : Proc → Finset PName
  | .tensor x y P         => {x} ∪ (P.fNames \ {y})
  | .parr x y P           => {x} ∪ (P.fNames \ {y})
  | .one x P              => {x} ∪ P.fNames
  | .bot x P              => {x} ∪ P.fNames
  | .cut x y P            => P.fNames \ {x, y}
  | ._par P Q              => P.fNames ∪ Q.fNames
  | .nil                  => {}

@[simp]
def Proc.names : Proc → Finset PName
  | .tensor x y P => {x, y} ∪ P.names
  | .parr x y P   => {x, y} ∪ P.names
  | .one x P      => {x} ∪ P.names
  | .bot x P      => {x} ∪ P.names
  | .cut x y P    => {x, y} ∪ P.names
  | ._par P Q      => P.names ∪ Q.names
  | .nil          => {}

def freshName (s : Finset Nat) : PName :=
  (Finset.fold Nat.max 0 id s) + 1

def renameBound old new P := rename (fun curr => if curr == old then new else curr) P

def renameBound2 old1 old2 new1 new2 P := renameBound old2 new2 (renameBound old1 new1 P)

-- Only bound names should be renamed and free names should match exactly
inductive AlphaEq : Proc → Proc → Prop where
  | nil : AlphaEq .nil .nil

  | par {P1 Q1 P2 Q2 : Proc} :
      AlphaEq P1 Q1 → AlphaEq P2 Q2 → AlphaEq (.par P1 P2) (.par Q1 Q2)

  | tensor {P Q : Proc} {x y x' y' : PName} : -- All PNames are free
      AlphaEq P Q → AlphaEq (.tensor x y P) (.tensor x' y' Q)
      → x = x' → y = y' → AlphaEq (.tensor x y P) (.tensor x' y' Q)

  | one {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.one x P) (.one x' Q)

  | bot {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.bot x P) (.bot x' Q)

  | parr {P Q : Proc} {x y x' y' : PName} -- x x' are Free, y y' are bound
      (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
        AlphaEq (.parr x y P) (.parr x' y' Q)

  | cut {P Q : Proc} {x y x' y' : PName} -- x y x' y' are all bound
      (w1 w2 : PName) (hFresh : w1 ∉ P.names ∪ Q.names ∧ w2 ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound2 x y w1 w2 P) (renameBound2 x' y' w1 w2 Q) →
        AlphaEq (.cut x y P) (.cut x' y' Q)

notation P " =ₐ " Q => AlphaEq P Q

-- TODO:
-- Reflexivity

-- Symmetry
-- @[simp]
-- theorem AlphaEq.symm {P Q : Proc} (h : AlphaEq P Q) : AlphaEq Q P := by
--   induction h
--   case refl => sorry
--   case tensor => sorry
--   case parr => sorry
--   case one => sorry
--   case bot => sorry
--   case cut => sorry
--   case par => sorry

-- -- Transitivity
-- @[simp]
-- theorem AlphaEq.trans {P Q R : Proc} (h₁ : AlphaEq P R) (h₂ : AlphaEq R Q) : AlphaEq P Q := by
--   induction h₁
--   case refl => exact h₂
--   case tensor => sorry
--   case parr => sorry
--   case one => sorry
--   case bot => sorry
--   case cut => sorry
--   case par => sorry

-- instance : Equivalence AlphaEq :=
-- { refl := @AlphaEq.refl,
--   symm := AlphaEq.symm,
--   trans := AlphaEq.trans}

------------------------------------------ TYPES  ------------------------------------------

abbrev Atom := Nat

inductive Types : Type where
  | atom      (a : Atom)      -- named type, like A, B, ...
  | atomDual  (a : Atom)      -- dual of a named type
  | tensor    (A B : Types)   -- t₁ ⊗ t₂ (send)
  | parr      (A B : Types)   -- t₁ ⅋ t₂ (receive)
  | one                       -- 𝟙 (empty output, unit for ⊗)
  | bot                       -- ⊥ (empty send, unit for ⅋)
deriving DecidableEq

infixr:95 " ⊗ " => Types.tensor
infixr:95 " ⅋ " => Types.parr
notation:100 "𝟙" => Types.one
notation:100 "⊥" => Types.bot

private def reprTypesAux : Types → Nat → String
  | .atom a, _ => s!"A{a}"
  | .atomDual a, _ => s!"A{a}ᗮ"
  | .tensor A B, _ => s!"({reprTypesAux A 0} ⊗ {reprTypesAux B 0})"
  | .parr A B, _ => s!"({reprTypesAux A 0} ⅋ {reprTypesAux B 0})"
  | .one, _ => "𝟙"
  | .bot, _ => "⊥"

instance : Repr Types where
  reprPrec A _ := reprTypesAux A 0

instance : ToString Types where
  toString t := reprStr t

def Types.pos : Types → Prop
  | atom _ => True
  | one => True
  | tensor _ _ => True
  -- | oplus _ _ => True
  -- | bang _ => True
  -- | zero => True
  | _ => False

def Types.neg : Types → Prop
  | atomDual _ => True
  | bot => True
  | parr _ _ => True
  -- | top => True
  -- | .with _ _ => True
  -- | quest _ => True
  | _ => False

instance Types.posDecidable (A : Types) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negDecidable (A : Types) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

@[simp]
def Types.dual : Types → Types
  | .tensor A B => .parr (dual A) (dual B)
  | .parr A B   => .tensor (dual A) (dual B)
  | .one        => .bot
  | .bot        => .one
  | .atom a     => .atomDual a
  | .atomDual a => .atom a

notation:max A "ᗮ" => Types.dual A

@[simp]
theorem Types.dual.neq (A : Types) : A ≠ Aᗮ := by
  cases A <;> simp [dual]

@[simp]
theorem dual.inj (A B : Types) : Aᗮ = Bᗮ ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem dual.involution (A : Types) : Aᗮᗮ = A := by
  induction A <;> simp [*]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env := Finset (PName × Types)

abbrev EmptyEnv : Env := ∅

/- FIXME: eval does not work since non-computable -/
noncomputable instance : Repr Env where
  reprPrec (Γ : Env) _ :=
    if Γ = ∅ then "∅"
    else
      let entries := Γ.toList.map (fun (x, A) => s!"{x} ∶ {reprStr A}")
      String.intercalate "‚ " entries

noncomputable instance : ToString Env where
  toString e := reprStr e

def Env.mk (x : PName) (A : Types) : Env :=
  {(x, A)}

infixr:90 " ∶ " => Env.mk

def Env.linear (Δ : Env) : Prop :=
  (Δ.image Prod.fst).card = Δ.card

def Env.names (Δ : Env) : Finset (PName) :=
  (Δ.image Prod.fst)

def Env.disjoint (Δ Γ : Env) : Prop :=
  (Δ.image Prod.fst ∩ Γ.image Prod.fst).card = 0

noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
  -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

notation Δ "⸨" x "⸩ₑ" => Env.lookup Δ x

-- Order independent equality for environments
@[simp]
def Env.Eq (Δ Γ : Env) : Prop :=
  ∀ x : (PName), Δ⸨x⸩ₑ = Γ⸨x⸩ₑ

notation Δ " =ₑ " Γ => Env.Eq Δ Γ

-- Eq reflexivity
@[simp]
theorem Env.Eq_refl (Δ : Env) : Δ =ₑ Δ :=
  fun _ => rfl

-- Eq symmetry
@[simp]
theorem Env.Eq_symm (Δ Γ : Env) (h : Δ =ₑ Γ) : Γ =ₑ Δ :=
  fun x => (h x).symm

-- Eq transitivity
@[simp]
theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Δ =ₑ Γ) (h₂ : Γ =ₑ Ε) : Δ =ₑ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence Env.Eq :=
⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

infixr:85 "‚ " => Env.merge

-- Merge identity
@[simp]
theorem Env.merge_unitR (Δ : Env) : Δ‚ ∅ = Δ := by
  simp [Env.merge]

@[simp]
theorem Env.merge_unitL (Δ : Env) : ∅‚ Δ = Δ := by
  simp [Env.merge]

-- Merge commutivity
-- theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Γ Δ := by
@[simp]
theorem Env.merge_comm (Δ Γ : Env) : Δ‚ Γ = Γ‚ Δ := by
  simp [Env.merge]
  simp [Finset.union_comm]

-- Merge associativity
@[simp]
theorem Env.merge_assoc (Δ Γ Ε : Env) : (Δ‚ Γ)‚ Ε = Δ‚ (Γ‚ Ε) := by
  simp [Env.merge]

@[simp]
lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
  (Γ‚ Δ)‚ Ξ = (Γ‚ Ξ)‚ Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := ∅

notation:max "⦃" Δ "⦄" => ({Δ} : HyperEnv)

-- Coercion makes extending a hyperenv with env and merging the same
-- and env1 |ₕ env2 => hyperenv due to envs being lifted to hyperenv
-- instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

/- FIXME: eval does not work since non-computable -/
open Lean in
noncomputable instance : Repr HyperEnv where
  reprPrec (𝒢 : HyperEnv) _ :=
    if 𝒢 = ∅ then "∅"
    else
      let entries := 𝒢.toList.map repr
      Format.joinSep entries " |ₕ "

noncomputable instance : ToString HyperEnv where
  toString g := reprStr g

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
  ∀ Δ ∈ 𝒢, Δ.linear ∧                               -- ensure each env is linear
  pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
  Finset.fold (· ∪ ·) ∅ Env.names 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
  (𝒢.toList.find? (fun Δ => Δ⸨x⸩ₑ ≠ none)) >>= fun Δ  => Δ⸨x⸩ₑ

notation:60 𝒢 "⸨" x "⸩ₕ" => HyperEnv.lookup 𝒢 x

def HyperEnv.disjoint (𝒢 ℋ : HyperEnv) : Prop :=
  -- 1. ensure both hyperenvs are lienar
  -- 2. ensure disjoint env names
  -- 3. ensure no duplicate definitions across hyperenvs
    -- s.t. an unambigous lookup in the individual hyperenvs
    -- yields an unambigous lookupin the merged hyperenv
    -- i.e. the intersection of their defined names is empty
  𝒢.linear ∧ ℋ.linear ∧
  (𝒢 ∩ ℋ).card = 0 ∧
  (𝒢.names ∩ ℋ.names).card = 0

-- Order independent equality for hyper-environments
@[simp]
def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
  -- (1) 𝒢 and ℋ must define the same names
  -- (2) The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  ∀ x ∈ HyperEnv.names 𝒢, 𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ

notation 𝒢 " =ₕ " ℋ => HyperEnv.Eq 𝒢 ℋ

-- Eq reflexivity
@[simp]
theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : 𝒢 =ₕ 𝒢 := by
  simp

-- Eq symmetry
@[simp]
theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : 𝒢 =ₕ ℋ) : ℋ =ₕ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- Eq transitivity
@[simp]
theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : 𝒢 =ₕ ℋ) (h₂ : ℋ =ₕ 𝒦) :
  𝒢 =ₕ 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
    calc
      𝒢⸨x⸩ₕ = ℋ⸨x⸩ₕ := h₁_vals x hx
      _          = 𝒦⸨x⸩ₕ := h₂_vals x hxH

instance : Equivalence HyperEnv.Eq :=
⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

@[simp]
abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

infixr:55 " |ₕ " => HyperEnv.merge

-- Merge identity
@[simp]
theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by
  simp

@[simp]
theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by
  simp

-- Merge commutative
@[simp]
theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : 𝒢 |ₕ ℋ = ℋ |ₕ 𝒢 := by
  simp [Finset.union_comm]

-- Merge associativity
@[simp]
theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  (𝒢 |ₕ ℋ) |ₕ 𝒦 = 𝒢 |ₕ (ℋ |ₕ 𝒦) := by
  simp

--------------------------------------- TYPING RULES ---------------------------------------

inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
    ----------
    Typing ∅ 𝟘

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} :
    Typing 𝒢 P → Typing ℋ Q →
    --------------------------
     Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types) :
    Typing (𝒢 |ₕ {Γ‚ x ∶ A} |ₕ {Δ‚ y ∶ Aᗮ}) P →
    ---------------------------------------
        Typing (𝒢 |ₕ {Γ‚ Δ}) (𝑣⸨x, y⸩ P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types} :
    Typing ({Γ‚ y ∶ A} |ₕ {Δ‚ x ∶ B}) P →
    ---------------------------------
    Typing ({Γ‚ Δ‚ x ∶ A ⊗ B}) (x⟦y⟧.P)

  | one {P : Proc} {x : PName} :
        Typing ∅ P →
    --------------------
    Typing ({x ∶ 𝟙}) (x⟦⟧.P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
     Typing ({Γ‚ y ∶ A‚ x ∶ B}) P →
    -----------------------------
    Typing ({Γ‚ x ∶ A ⅋ B}) (x⸨y⸩.P)

  | bot {Γ : Env} {P : Proc} {x : PName} :
          Typing {Γ} P →
    ------------------------
    Typing ({Γ‚ x ∶ ⊥}) (x⸨⸩.P)

notation:50 "⊢ " P " ∷ " T => Typing T P --FIXME: This seems to not work that well when
                                         --writing but when Lean pretty prints it seems fine

----------------------------- TRANSITION RULES FOR DERIVATIONS -----------------------------

inductive Act : Type
  | one     (x : PName)     -- x[]
  | bot     (x : PName)     -- x()
  | tensor  (x y : PName)   -- x[y]
  | parr    (x y : PName)   -- x(y)
deriving Repr, DecidableEq

inductive Lbl : Type
  | tau                       -- τ
  | act   (a : Act)           -- l, for l ∈ Act
  | par   (l l' : Act)        -- l | l' for l, l' ∈ Act
deriving Repr, DecidableEq

abbrev Lbls := List Lbl

instance : Coe Act Lbl := ⟨Lbl.act⟩

@[simp]
def getNamesOfLbl (func : Act → Finset PName) : Lbl → Finset PName
  | .tau        => ∅                  -- names for τ
  | .act a      => func a             -- names for l with l ∈ Act
  | .par l l'   => func l ∪ func l'   -- names for l | l' with l, l' ∈ Act

@[simp]
def fNamesAct : Act -> Finset PName -- free names for a given action
  | .one x | .bot x | .tensor x _ | .parr x _ => {x}

@[simp]
def Lbl.fNames : Lbl → Finset PName :=
  getNamesOfLbl fNamesAct

@[simp]
def iNamesAct : Act → Finset PName -- introduced names for a given action
  | .one _ | .bot _          => {}
  | .tensor _ y | .parr _ y => {y}

@[simp]
def Lbl.iNames : Lbl → Finset PName :=
  getNamesOfLbl iNamesAct

@[simp]
def Lbl.fresh (xs : List PName) (l : Lbl) :=
  ∀ n ∈ xs, n ∉ l.fNames ∪ l.iNames

-- def Lbl.wf : Lbl → Prop
--   | Lbl.par l l' => (iNamesAct l) ∩ (iNamesAct l') = ∅
--   | _ => True

-- def Finset.prod (s₁ s₂ : Finset Act) : Finset (Act × Act) :=
--   (Finset.fold (· ∪ ·) ∅ (fun (a : Act) => s₂.image (fun (a' : Act) => (a, a'))) s₁)

-- def LblSet (acts : Finset Act) : Finset Lbl :=
--   let τ := ∅
--   let single := acts.image Lbl.act
--   let parallel :=
--     (Finset.prod acts acts)
--       |>.filter (fun (p : Act × Act) => (iNamesAct p.1) ∩ (iNamesAct p.2) = ∅)
--       |>.image (fun (p : Act × Act) => Lbl.par p.1 p.2)
--   τ ∪ single ∪ parallel

notation:80 x "⟦" y "⟧" => Act.tensor x y
notation:80 x "⟦⟧" => Act.one x
notation:80 x "⸨" y "⸩" => Act.parr x y
notation:80 x "⸨⸩" => Act.bot x
notation:70 "τ" => Lbl.tau
notation:70 l " |ₗ " l' => Lbl.par l l'

-- CHANGE LABELS TO USE THE DEFINED NOTATION...

inductive TypingStep : {Γ : HyperEnv} → {P : Proc} → Typing Γ P →
  Lbl → {Γ' : HyperEnv} → {P' : Proc} → Typing Γ' P' → Prop where
  | one
      {P : Proc} {x : PName} {𝒟 : Typing ∅ P} :
      TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
      {𝒟 : Typing ({Γ‚ x' ∶ A} |ₕ {Δ‚ x ∶ B}) P} :
      TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : PName} {𝒟 : Typing {Γ} P} :
      TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

  | parr
      {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
      {𝒟 : Typing ({Γ‚ x' ∶ A‚ x ∶ B}) P} :
      TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'} {ℰ : Typing ℋ Q}
      (h : TypingStep 𝒟 l 𝒟') (disj : (l.iNames) ∩ (Q.fNames) = ∅) :
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h : TypingStep ℰ l ℰ') (disj : (l.iNames) ∩ (P.fNames) = ∅) :
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {a a' : Act}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'}
      {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h₁ : TypingStep 𝒟 a 𝒟')
      (h₂ : TypingStep ℰ a' ℰ')
      (disj : ((Lbl.par a a').iNames ∩ (Proc.par P Q).fNames) = ∅) :
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) (a |ₗ a') (Typing.mix 𝒟' ℰ')

  | alpha_equiv
      {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing 𝒢 Q} {ℰ' : Typing 𝒢' Q'}
      (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
      -------------------------------------------------------
      TypingStep 𝒟 l ℰ'

  | one_bot
      {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
      {𝒟 : Typing (𝒢 |ₕ {x ∶ 𝟙} |ₕ {Γ‚ y ∶ ⊥}) P} {𝒟' : Typing (𝒢 |ₕ {Γ}) P'}
      (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
      ----------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 ∅ Γ P x y (𝟙) 𝒟) (τ) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
      {𝒟 : Typing (𝒢 |ₕ {(Γ‚ Δ)‚ x ∶ A ⊗ B} |ₕ {Ξ‚ y ∶ Aᗮ ⅋ Bᗮ}) P}
      {𝒟' : Typing ((𝒢 |ₕ {Γ‚ x ∶ B}) |ₕ {Δ‚ x' ∶ A} |ₕ {(Ξ‚ y ∶ Bᗮ)‚ y' ∶ Aᗮ}) P'}
      (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
      ----------------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 (Γ‚ Δ) Ξ P x y (A ⊗ B) 𝒟)
        (τ)
        (by
          let inner := Typing.cut (𝒢 |ₕ {Γ‚ x ∶ B}) Δ (Ξ‚ y ∶ Bᗮ) P' x' y' A 𝒟'
          rw [← Env.merge_assoc, HyperEnv.merge_assoc] at inner
          exact Typing.cut 𝒢 Γ (Δ‚ Ξ) (𝑣⸨x', y'⸩ P') x y B inner
        )

  | res
      {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
      {x y : PName} {A : Types} {l : Lbl}
      {𝒟 : Typing (𝒢 |ₕ {Γ‚ x ∶ A} |ₕ {Δ‚ y ∶ Aᗮ}) P}
      {𝒟' : Typing (𝒢' |ₕ {Γ'‚ x ∶ A} |ₕ {Δ'‚ y ∶ Aᗮ}) P'}
      (h : TypingStep 𝒟 l 𝒟')
      -- (disj : ∀ n ∈ [x, y], n ∉ l.fNames ∪ l.iNames)
      (disj : l.fresh [x, y]) :
      ----------------------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')

notation:50 𝒟 " -[" l "]->ₜ " 𝒟' => TypingStep 𝒟 l 𝒟'

open Lean PrettyPrinter in
@[app_unexpander Lbl.act]
def unexpandLblAct : Unexpander
  | `($_ $a) => pure a
  | _ => pure Syntax.missing

-------------------------- MULTI-TYPING-STEP-TRANSITIONS ---------------------------
notation:80 "ε" => (List.nil : Lbls)
notation:60 xs " ∷ₗ " x => List.concat (xs : Lbls) (x : Lbl)

lemma eq_concat_nil {l} :
  [l] = (ε ∷ₗ l) := by rfl

lemma cons_concat_eq {x xs y} :
  x :: (xs ∷ₗ y) = x :: (xs ∷ₗ y) := by simp

lemma append_concat_eq {xs ys y} :
  xs ++ (ys ∷ₗ y) = (xs ++ ys) ∷ₗ y := by simp

lemma cons_append_assoc {x : Lbl} {xs ys : Lbls} :
  x :: (xs ++ ys) = (x :: xs) ++ ys := by rfl

inductive MTST : {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
  Typing 𝒢 P → Lbls → Typing 𝒢' P' → Prop where
  | refl
    {𝒢 : HyperEnv} {P: Proc} {𝒟 : Typing 𝒢 P} :
    MTST 𝒟 (ε) 𝒟

  | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
    (𝒟  : Typing 𝒢  P) (𝒟' : Typing 𝒢' P') (𝒟'' : Typing 𝒢'' P'') :
    (MTST 𝒟 ls 𝒟'') → (𝒟'' -[l]->ₜ 𝒟') →
    -------------------------------------
          MTST 𝒟 (ls ∷ₗ l) 𝒟'

notation:50 𝒟 " -[" ls "]->>ₜ " 𝒟' => MTST 𝒟 ls 𝒟'

------------------------- PROC-FUCNTION & TRANSITION RULES -------------------------

def proc {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : Proc := P

inductive ProcStep : (P : Proc) → Lbl → (P' : Proc) → Prop where
  | one
      {P : Proc} {x : PName} :
      ProcStep (x⟦⟧.P) (x⟦⟧) P

  | tensor
      {P : Proc} {x x' : PName} :
      ProcStep (x⟦x'⟧.P) (x⟦x'⟧) P

  | bot
      {P : Proc} {x : PName} :
      ProcStep (x⸨⸩.P) (x⸨⸩) P

  | parr
      {P : Proc} {x x' : PName} :
      ProcStep (x⸨x'⸩.P) (x⸨x'⸩) P

  | par₁
      {P P' Q : Proc} {l : Lbl} :
      ProcStep P l P' → l.iNames ∩ Q.fNames = ∅ →
      -------------------------------------------
      ProcStep (P |ₚ Q) l (P' |ₚ Q)

  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStep Q l Q' → l.iNames ∩ P.fNames = ∅ →
      --------------------------------------------
      ProcStep (P |ₚ Q) l (P |ₚ Q')

  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStep P l P' → ProcStep Q l' Q' →
      (l |ₗ l').iNames ∩ (P |ₚ Q).fNames = ∅  →
      ----------------------------------------
      ProcStep (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

  | alpha_equiv
      {P Q Q' : Proc} {l : Lbl} :
      (P =ₐ Q) → ProcStep Q l Q' →
      -------------------------------
      ProcStep P l Q'

  | one_bot
      {P P' : Proc} {x y : PName} :
      ProcStep P (x⟦⟧ |ₗ y⸨⸩) P' →
      --------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) P'

  | tensor_parr
      {P P' : Proc} {x x' y y' : PName} :
      ProcStep P (x⟦x'⟧ |ₗ y⸨y'⸩) P' →
      --------------------------------------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ (𝑣⸨x', y'⸩ P'))

  | res
      {P P' : Proc} {x y : PName} {l : Lbl} :
      ProcStep P l P' → l.fresh [x, y] →
      -------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) P'

notation:50 P " -[" l "]->ₚ " P' => ProcStep P l P'

inductive MPST : (P : Proc) → Lbls → (P' : Proc) → Prop where
  | refl
    {P : Proc} :
    ------------
    MPST P (ε) P

  | stepR {l : Lbl} {ls : Lbls} {P P'' P' : Proc} :
    (MPST P ls P'') → (P'' -[l]->ₚ P') →
    ----------------------------------
          MPST P (ls ∷ₗ l) P'

notation:50 P " -[" ls "]->>ₚ " P' => MPST P ls P'

------------------------- ENV-FUCNTION & TRANSITION RULES --------------------------

def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : PName} :
      EnvStep ⦃x ∶ 𝟙⦄ (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep ⦃Γ‚ Δ‚ x ∶ A ⊗ B⦄ (x⟦x'⟧) (⦃Γ‚ x'∶ A⦄ |ₕ ⦃Δ‚ x ∶ B⦄)

  | bot
      {Γ : Env} {x : PName} :
      EnvStep ⦃Γ‚ x ∶ ⊥⦄ (x⸨⸩) ⦃Γ⦄

  | parr
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep ⦃Γ‚ x ∶ A ⅋ B⦄ (x⸨x'⸩) (⦃Γ‚ x' ∶ A⦄ |ₕ ⦃Δ‚ x ∶ B⦄)

  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStep 𝒢 l 𝒢' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStep ℋ l ℋ' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStep 𝒢 l 𝒢' → EnvStep ℋ l' ℋ' →
      ------------------------------------
      EnvStep (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')

  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {x y : PName} :
      EnvStep (𝒢 |ₕ ⦃x ∶ 𝟙⦄ |ₕ ⦃Γ‚ y ∶ ⊥⦄) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ ⦃Γ⦄) →
      ----------------------------------------------------------
      EnvStep (𝒢 |ₕ ⦃Γ⦄) (τ) (𝒢 |ₕ ⦃Γ⦄)

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': PName} {A B : Types} :
      EnvStep
        (𝒢 |ₕ ⦃Γ‚ Δ‚ x ∶ A ⊗ B⦄ |ₕ ⦃Ξ‚ y ∶ Aᗮ ⅋ Bᗮ⦄)
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ ⦃Γ‚ x' ∶ A⦄ |ₕ ⦃Δ‚ x ∶ B⦄ |ₕ ⦃Ξ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ⦄) →
      --------------------------------------------------------
      EnvStep (𝒢 |ₕ ⦃Γ‚ Δ‚ Ξ⦄) (τ) (𝒢 |ₕ ⦃Γ‚ Δ‚ Ξ⦄)

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : PName} {A B : Types} {l : Lbl} :
      EnvStep (𝒢 |ₕ ⦃Γ‚ x ∶ Aᗮ⦄ |ₕ ⦃Δ‚ y ∶ A⦄) (l) (𝒢' |ₕ ⦃Γ'‚ x ∶ Aᗮ⦄ |ₕ ⦃Δ'‚ y ∶ A⦄) →
      ----------------------------------------------------------------------------
      EnvStep (𝒢 |ₕ ⦃Γ‚ Δ⦄) l (𝒢' |ₕ ⦃Γ'‚ Δ'⦄)
