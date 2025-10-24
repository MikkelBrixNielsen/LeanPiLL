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
  | par     (P Q : Proc)               -- P | Q
  | nil                                -- 𝟘
deriving Repr, DecidableEq

abbrev Renaming := PName → PName

def rename (ρ : Renaming) : Proc → Proc
  | .tensor x y P => .tensor (ρ x) (ρ y) (rename ρ P)
  | .parr x y P   => .parr (ρ x) (ρ y) (rename ρ P)
  | .one x P      => .one (ρ x) (rename ρ P)
  | .bot x P      => .bot (ρ x) (rename ρ P)
  | .cut x y P    => .cut (ρ x) (ρ y) (rename ρ P)
  | .par P Q      => .par (rename ρ P) (rename ρ Q)
  | .nil          => .nil

@[simp]
def Proc.fNames : Proc → Finset PName
  | .tensor x y P         => {x} ∪ (P.fNames \ {y})
  | .parr x y P           => {x} ∪ (P.fNames \ {y})
  | .one x P              => {x} ∪ P.fNames
  | .bot x P              => {x} ∪ P.fNames
  | .cut x y P            => P.fNames \ {x, y}
  | .par P Q              => P.fNames ∪ Q.fNames
  | .nil                  => {}

@[simp]
def Proc.names : Proc → Finset PName
  | .tensor x y P => {x, y} ∪ P.names
  | .parr x y P   => {x, y} ∪ P.names
  | .one x P      => {x} ∪ P.names
  | .bot x P      => {x} ∪ P.names
  | .cut x y P    => {x, y} ∪ P.names
  | .par P Q      => P.names ∪ Q.names
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
deriving Repr, DecidableEq

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

@[simp]
theorem Types.dual.neq (A : Types) : A ≠ dual A := by
  cases A <;> simp [dual]

@[simp]
theorem dual.inj (A B : Types) : Types.dual A = Types.dual B ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem dual.involution (A : Types) : Types.dual (Types.dual A) = A := by
  induction A <;> simp [*]

--------------------------------------- ENVIRONMENTS ---------------------------------------

abbrev Env := Finset (PName × Types)

abbrev EmptyEnv : Env := ∅

def Env.mk (x : PName) (A : Types) : Env :=
  {(x, A)}

def Env.linear (Δ : Env) : Prop :=
  (Δ.image Prod.fst).card = Δ.card

def Env.names (Δ : Env) : Finset (PName) :=
  (Δ.image Prod.fst)

def Env.disjoint (Δ Γ : Env) : Prop :=
  (Δ.image Prod.fst ∩ Γ.image Prod.fst).card = 0

noncomputable def Env.lookup (Δ : Env) (x : PName) : Option Types :=
  -- Finset.fold (· ∪ ·) none (fun p => if p.fst = x then p.snd else none) Δ
  (Δ.toList.find? (fun p => p.fst = x)).map Prod.snd

-- Order independent equality for environments
def Env.Eq (Δ Γ : Env) : Prop :=
  ∀ x : (PName), Δ.lookup x = Γ.lookup x

-- Eq reflexivity
@[simp]
theorem Env.Eq_refl (Δ : Env) : Env.Eq Δ Δ :=
  fun _ => rfl

-- Eq symmetry
@[simp]
theorem Env.Eq_symm (Δ Γ : Env) (h : Env.Eq Δ Γ) : Env.Eq Γ Δ :=
  fun x => (h x).symm

-- Eq transitivity
@[simp]
theorem Env.Eq_trans (Δ Γ Ε : Env) (h₁ : Env.Eq Δ Γ) (h₂ : Env.Eq Γ Ε) : Env.Eq Δ Ε :=
  fun x => Eq.trans (h₁ x) (h₂ x)

instance : Equivalence Env.Eq :=
⟨Env.Eq_refl, @Env.Eq_symm, @Env.Eq_trans⟩

def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

-- Merge identity
@[simp]
theorem Env.merge_unitR (Δ : Env) : Δ.merge EmptyEnv = Δ := by
  simp [Env.merge]

@[simp]
theorem Env.merge_unitL (Δ : Env) : Env.merge EmptyEnv Δ = Δ := by
  simp [Env.merge]

-- Merge commutivity
-- theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Γ Δ := by
@[simp]
theorem Env.merge_comm (Δ Γ : Env) : Δ.merge Γ = Γ.merge Δ := by
  simp [Env.merge]
  simp [Finset.union_comm]

-- Merge associativity
@[simp]
theorem Env.merge_assoc (Δ Γ Ε : Env) : (Δ.merge Γ).merge Ε = Δ.merge (Γ.merge Ε) := by
  simp [Env.merge]

lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
  (Γ.merge Δ).merge Ξ = (Γ.merge Ξ).merge Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := {}

-- Coercion makes extending a hyperenv with env and merging the same
-- and env1 |ₕ env2 => hyperenv due to envs being lifted to hyperenv
instance : Coe Env HyperEnv := ⟨fun Γ => {Γ}⟩

def pairwise {α : Type} (r : α → α → Prop) (s : Finset α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, y ≠ x → r x y

def HyperEnv.linear (𝒢 : HyperEnv) : Prop :=
  ∀ Δ ∈ 𝒢, Δ.linear ∧                               -- ensure each env is linear
  pairwise (fun Δ Γ => Δ.disjoint Γ) 𝒢              -- ensure pairwise env disjointness

def HyperEnv.names (𝒢 : HyperEnv) : Finset PName :=
  Finset.fold (· ∪ ·) ∅ Env.names 𝒢

-- Lookup method for finding the type of a name in the hyperenvironment
noncomputable def HyperEnv.lookup (𝒢 : HyperEnv) (x : PName) : Option Types :=
  (𝒢.toList.find? (fun Δ => Δ.lookup x ≠ none)) >>= fun Δ  => Δ.lookup x

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
def HyperEnv.Eq (𝒢 ℋ : HyperEnv) : Prop :=
  -- 𝒢 and ℋ must define the same names
  HyperEnv.names 𝒢 = HyperEnv.names ℋ ∧
  -- The typing of all defined names must match i.e. ∀ x, 𝒢(x) = ℋ(x)
  ∀ x ∈ HyperEnv.names 𝒢, 𝒢.lookup x = ℋ.lookup x

-- Eq reflexivity
@[simp]
theorem HyperEnv.Eq_refl (𝒢 : HyperEnv) : HyperEnv.Eq 𝒢 𝒢 := by
  simp [HyperEnv.Eq]

-- Eq symmetry
@[simp]
theorem HyperEnv.Eq_symm (𝒢 ℋ : HyperEnv) (h : HyperEnv.Eq 𝒢 ℋ) : HyperEnv.Eq ℋ 𝒢 := by
  rcases h with ⟨h_names, h_vals⟩
  refine ⟨h_names.symm, ?vals⟩
  intro x hx
  rw [h_names] at h_vals
  apply (h_vals x hx).symm

-- Eq transitivity
@[simp]
theorem HyperEnv.Eq_trans (𝒢 ℋ 𝒦 : HyperEnv) (h₁ : HyperEnv.Eq 𝒢 ℋ) (h₂ : HyperEnv.Eq ℋ 𝒦) :
  HyperEnv.Eq 𝒢 𝒦 := by
  rcases h₁ with ⟨h₁_names, h₁_vals⟩
  rcases h₂ with ⟨h₂_names, h₂_vals⟩
  refine ⟨?names, ?vals⟩
  · rw [h₁_names, h₂_names]
  · intro x hx
    have hxH : x ∈ ℋ.names := by rw [← h₁_names]; exact hx
    calc
      𝒢.lookup x = ℋ.lookup x := h₁_vals x hx
      _          = 𝒦.lookup x := h₂_vals x hxH

instance : Equivalence HyperEnv.Eq :=
⟨HyperEnv.Eq_refl, @HyperEnv.Eq_symm, @HyperEnv.Eq_trans⟩

@[simp]
abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ∪ ℋ

-- Merge identity
@[simp]
theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : HyperEnv.merge EmptyHyperEnv 𝒢 = 𝒢 := by
  simp

@[simp]
theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : HyperEnv.merge 𝒢 EmptyHyperEnv = 𝒢 := by
  simp

-- Merge commutative
@[simp]
theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : HyperEnv.merge 𝒢 ℋ = HyperEnv.merge ℋ 𝒢 := by
  simp [Finset.union_comm]

-- Merge associativity
@[simp]
theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) :
  HyperEnv.merge (HyperEnv.merge 𝒢 ℋ) 𝒦 = HyperEnv.merge 𝒢 (HyperEnv.merge ℋ 𝒦) := by
  simp

----------------------------------------- NOTATION -----------------------------------------

/- PROC -/
notation:80 x "⟦" y "⟧" "." P:80 => Proc.tensor x y P
notation:80 x "⟦⟧" "." P:80 => Proc.one x P
notation:80 x "⸨" y "⸩" "." P:80 => Proc.parr x y P
notation:80 x "⸨⸩" "." P:80 => Proc.bot x P
notation:60 "𝑣" "⸨" x ", " y "⸩ " P => Proc.cut x y P
notation "𝟘" => Proc.nil
infixr:65 " |ₚ " => Proc.par

/- TYPING -/
infixr:95 " ⊗ " => Types.tensor
infixr:95 " ⅋ " => Types.parr
notation:100 "𝟙" => Types.one
notation:100 "⊥" => Types.bot
notation:max A "ᗮ" => Types.dual A

/- ENV -/
infixr:90 " ∶ " => Env.mk
infixr:85 "‚ " => Env.merge

/- HYPERENV -/
notation:60 𝒢 "⸨" x "⸩" => HyperEnv.lookup 𝒢 x
infixr:55 " |ₕ " => HyperEnv.merge

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
    Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
    ---------------------------------------
        Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types} :
    Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
    ---------------------------------
    Typing (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦y⟧.P)

  | one {P : Proc} {x : PName} :
        Typing ∅ P →
    --------------------
    Typing (x ∶ 𝟙) (x⟦⟧.P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
     Typing (Γ‚ y ∶ A‚ x ∶ B) P →
    -----------------------------
    Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩.P)

  | bot {Γ : Env} {P : Proc} {x : PName} :
          Typing Γ P →
    ------------------------
    Typing (Γ‚ x ∶ ⊥) (x⸨⸩.P)

notation:50 "⊢ " P " ∷ " T => Typing T P -- FIXME: This seems to not work that well when writing
                                         -- but when Lean pretty prints it seems fine

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

inductive TypingStep : {Γ : HyperEnv} → {P : Proc} → Typing Γ P →
  Lbl → {Γ' : HyperEnv} → {P' : Proc} → Typing Γ' P' → Prop where
  | one
      {P : Proc} {x : PName} {𝒟 : Typing ∅ P} :
      TypingStep (Typing.one 𝒟) (Lbl.act (Act.one x)) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types} {𝒟 : Typing (Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B) P} :
      TypingStep (Typing.tensor 𝒟) (Lbl.act (Act.tensor x x')) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : PName} {𝒟 : Typing Γ P} :
      TypingStep (Typing.bot 𝒟) (Lbl.act (Act.bot x)) 𝒟

  | parr
      {Γ : Env} {P : Proc} {x x' : PName} {A B : Types} {𝒟 : Typing (Γ‚ x' ∶ A‚ x ∶ B) P} :
      TypingStep (Typing.parr 𝒟) (Lbl.act (Act.parr x x')) 𝒟

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'} {ℰ : Typing ℋ Q}
      (h : TypingStep 𝒟 l 𝒟') (disj : (l.iNames) ∩ (Q.fNames) = ∅) :
      --------------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h : TypingStep ℰ l ℰ') (disj : (l.iNames) ∩ (P.fNames) = ∅) :
      --------------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {a a' : Act}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'}
      {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h₁ : TypingStep 𝒟 (Lbl.act a) 𝒟')
      (h₂ : TypingStep ℰ (Lbl.act a') ℰ')
      (disj : ((Lbl.par a a').iNames ∩ (Proc.par P Q).fNames) = ∅) :
      -----------------------------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) (Lbl.par a a') (Typing.mix 𝒟' ℰ')

  | alpha_equiv
      {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing 𝒢 Q} {ℰ' : Typing 𝒢' Q'}
      (h₁ : AlphaEq P Q)
      (h₂ : TypingStep ℰ l ℰ') :
      -------------------------------------------------------
      TypingStep 𝒟 l ℰ'

  | one_bot
      {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
      {𝒟 : Typing (𝒢 |ₕ x ∶ 𝟙 |ₕ Γ‚ y ∶ ⊥) P} {𝒟' : Typing (𝒢 |ₕ Γ) P'}
      (h : TypingStep 𝒟 (Lbl.par (Act.one x) (Act.bot y)) 𝒟') :
      ----------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 ∅ Γ P x y (𝟙) 𝒟) (Lbl.tau) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
      {𝒟 : Typing (𝒢 |ₕ (Γ‚ Δ)‚ x ∶ A ⊗ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ) P}
      {𝒟' : Typing ((𝒢 |ₕ {Γ‚ x ∶ B}) |ₕ {Δ‚ x' ∶ A} |ₕ {(Ξ‚ y ∶ Bᗮ)‚ y' ∶ Aᗮ}) P'}
      (h : TypingStep 𝒟 (Lbl.par (Act.tensor x x') (Act.parr y y')) 𝒟') :
      -----------------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 (Γ‚ Δ) Ξ P x y (A ⊗ B) 𝒟)
        Lbl.tau
        (by
          let inner := Typing.cut (𝒢 |ₕ Γ‚ x ∶ B) Δ (Ξ‚ y ∶ Bᗮ) P' x' y' A 𝒟'
          rw [← Env.merge_assoc, HyperEnv.merge_assoc] at inner
          exact Typing.cut 𝒢 Γ (Δ‚ Ξ) (𝑣⸨x', y'⸩ P') x y B inner
        )

  | res
      {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {x y : PName} {A : Types} {l : Lbl}
      {𝒟 : Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P}
      {𝒟' : Typing (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ) P'}
      (h : TypingStep 𝒟 l 𝒟')
      (disj : x ∉ l.fNames ∪ l.iNames ∧ y ∉ l.fNames ∪ l.iNames) :
      ------------------------------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')

notation:50 𝒟 " -[" l "]-> " 𝒟' => TypingStep 𝒟 l 𝒟'
notation:80 x "⟦" y "⟧" => Act.tensor x y
notation:80 x "⟦⟧" => Act.one x
notation:80 x "⸨" y "⸩" => Act.parr x y
notation:80 x "⸨⸩" => Act.bot x
notation:70 "τ" => Lbl.tau
notation:70 l " |ₗ " l' => Lbl.par l l'

open Lean PrettyPrinter in
@[app_unexpander Lbl.act]
def unexpandLblAct : Unexpander
  | `($_ $a) => pure a
  | _ => pure Syntax.missing

----------------------------------- MULTISTEP-TRANSITIONS ----------------------------------
notation:80 "ε" => (List.nil : Lbls)
notation:60 xs " ∷ₘ " x => List.concat (xs : Lbls) (x : Lbl)

lemma eq_concat_nil {l} :
  [l] = (ε ∷ₘ l) := by rfl

lemma cons_concat_eq {x xs y} :
  x :: (xs ∷ₘ y) = x :: (xs ∷ₘ y) := by simp

lemma append_concat_eq {xs ys y} :
  xs ++ (ys ∷ₘ y) = (xs ++ ys) ∷ₘ y := by simp

lemma cons_append_assoc {x : Lbl} {xs ys : Lbls} :
  x :: (xs ++ ys) = (x :: xs) ++ ys := by rfl

inductive MTST : {𝒢 𝒢' : HyperEnv} → {P P' : Proc} →
  Typing 𝒢 P → Lbls → Typing 𝒢' P' → Prop where
  | refl
    {𝒢 : HyperEnv} {P: Proc} (𝒟 : Typing 𝒢 P) :
    ------------
    MTST 𝒟 (ε) 𝒟

  | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢' 𝒢'' : HyperEnv} {P P' P'' : Proc}
    (𝒟  : Typing 𝒢  P) (𝒟' : Typing 𝒢' P') (𝒟'' : Typing 𝒢'' P'') :
    (MTST 𝒟 ls 𝒟') → (𝒟' -[l]-> 𝒟'') →
    ----------------------------------
          MTST 𝒟 (ls ∷ₘ l) 𝒟''

notation:50 𝒟 " -[" ls "]->> " 𝒟' => MTST 𝒟 ls 𝒟'
