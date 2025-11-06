import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold

-- inductive Typing : Finset (Nat) → Prop where
--   | global {Γ : Finset Nat} :
--       Typing Γ

--   | bot {Γ : Finset Nat} {x : Nat} :
--       Typing Γ →
--       ----------------
--       Typing (Γ ∪ {x})

--   | parr {Γ : Finset Nat} {x y : Nat} :
--     Typing (Γ ∪ {y} ∪ {x}) → Typing (Γ ∪ {x + y})

-- inductive TypingStep : {𝒢 : Finset Nat} → Typing 𝒢 → (l : List Nat) →
--   {𝒢' : Finset Nat} → Typing 𝒢' → Prop where
--    | bot
--       {Γ : Finset Nat} {x : Nat} (𝒟 : Typing (Γ)) :
--       TypingStep (Typing.bot 𝒟) ([x]) (𝒟)

--   | parr
--       {Γ : Finset Nat} {x y : Nat} (𝒟 : Typing (Γ ∪ {y} ∪ {x})) :
--       ------------------------------------------------------------
--       TypingStep (Typing.parr 𝒟) [x, y] 𝒟

-- notation:50 𝒟 " -[" l "]-> " 𝒟' => TypingStep 𝒟 l 𝒟'

-- example {Γ : Finset ℕ} {x y : ℕ}
--   (ℱ : Typing (Γ ∪ {x + y})) (ℱ' : Typing (Γ ∪ {y} ∪ {x})) :
--   ℱ -[[x, y]]-> ℱ' := by
--   apply TypingStep.parr




/- Processes -/
abbrev PName := Nat

inductive Proc : Type where
  | tensor  (x y : PName) (P : Proc)   -- x[y].P
  | parr    (x y : PName) (P : Proc)   -- x(y).P
  | one     (x : PName) (P : Proc)     -- x[].P
  | bot     (x : PName) (P : Proc)     -- x().P
  | cut     (x y : PName) (P : Proc)   -- 𝒗xy P
  | par     (P Q : Proc)               -- P | Q
  | nil                                -- 𝟘
deriving DecidableEq

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

/- TYPES -/
abbrev Atom := Nat

inductive Types : Type where
  | atom      (a : Atom)      -- named type, like A, B, ...
  | atomDual  (a : Atom)      -- dual of a named type
  | tensor    (A B : Types)   -- t₁ ⊗ t₂ (send)
  | parr      (A B : Types)   -- t₁ ⅋ t₂ (receive)
  | one                       -- 𝟙 (empty output, unit for ⊗)
  | bot                       -- ⊥ (empty send, unit for ⅋)
deriving DecidableEq

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
theorem Types.dual.neq (A : Types) : A ≠ Types.dual A := by
  cases A <;> simp [dual]

@[simp]
theorem dual.inj (A B : Types) : A.dual = B.dual ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem dual.involution (A : Types) : A.dual.dual = A := by
  induction A <;> simp [*]


/- ENVIRONMENTS -/
abbrev Env := Finset (PName × Types)
@[simp] theorem Env.merge_unitR (Δ : Env) : Δ ∪ ∅ = Δ := by simp

@[simp] theorem Env.merge_unitL (Δ : Env) : ∅ ∪ Δ = Δ := by simp

@[simp] theorem Env.merge_comm (Δ Γ : Env) : Δ ∪ Γ = Γ ∪ Δ := by simp [Finset.union_comm]

@[simp] theorem Env.merge_assoc (Δ Γ Ε : Env) : (Δ ∪ Γ) ∪ Ε = Δ ∪ (Γ ∪ Ε) := by simp

@[simp] lemma Env.merge_swap_last (Γ Δ Ξ : Env) : (Γ ∪ Δ) ∪ Ξ = (Γ ∪ Ξ) ∪ Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]


/- HYPER ENVIRONMENTS -/
abbrev HyperEnv := Finset (Env)

@[simp] theorem HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ ∪ 𝒢 = 𝒢 := by simp

@[simp] theorem HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 ∪ ∅ = 𝒢 := by simp

@[simp] theorem HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : 𝒢 ∪ ℋ = ℋ ∪ 𝒢 := by simp [Finset.union_comm]

@[simp] theorem HyperEnv.merge_assoc (𝒢 ℋ 𝒦 : HyperEnv) : (𝒢 ∪ ℋ) ∪ 𝒦 = 𝒢 ∪ (ℋ ∪ 𝒦) := by simp


/- TYPINGS -/
inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
      -----------------
      Typing ∅ Proc.nil

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} :
      Typing 𝒢 P → Typing ℋ Q →
      --------------------------
      Typing (𝒢 ∪ ℋ) (Proc.par P Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types) :
      Typing (𝒢 ∪ {Γ ∪ {(x, A)}} ∪ {Δ ∪ {(y, A.dual)}}) P →
      ------------------------------------------------------
      Typing (𝒢 ∪ {Γ ∪ Δ}) (Proc.cut x y P)

  | one {P : Proc} {x : PName} :
      Typing ∅ P →
      ----------------------------------------
      Typing {{(x, Types.one)}} (Proc.one x P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types} :
      Typing ({Γ ∪ {(y, A)}} ∪ {Δ ∪ {(x, B)}}) P →
      --------------------------------------------------------------
      Typing ({Γ ∪ Δ ∪ {(x, Types.tensor A B)}}) (Proc.tensor x y P)

  | bot {Γ : Env} {P : Proc} {x : PName} :
      Typing {Γ} P →
      --------------------------------------------
      Typing {Γ ∪ {(x, Types.bot)}} (Proc.bot x P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
      Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} P →
      -------------------------------------------------------
      Typing {Γ ∪ {(x, (Types.parr A B))}} (Proc.parr x y P)


/- LABELS -/
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


/- TYPING TRANSITIONS-/
-- FIXME: Make arrow based instead premise → premise → ... → premise → conlcusion
inductive TypingStep : {𝒢 : HyperEnv} → {P : Proc} → Typing 𝒢 P → (l : Lbl) →
  {𝒢' : HyperEnv} → {P : Proc} → Typing 𝒢' P → Prop where
  | one
      {P : Proc} {x : PName} {𝒟 : Typing ∅ P} :
      TypingStep (Typing.one 𝒟) (Lbl.act (Act.one x)) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
      {𝒟 : Typing ({Γ ∪ {(x', A)}} ∪ {Δ ∪ {(x, B)}}) P} :
      TypingStep (Typing.tensor 𝒟) (Lbl.act (Act.tensor x x')) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : PName} (𝒟 : Typing {Γ} P) :
      TypingStep (Typing.bot (x := x) 𝒟) (Lbl.act (Act.bot x)) (𝒟)

  | parr
      {Γ : Env} {P : Proc} {x x' : PName} {A B : Types} :
      (𝒟 : Typing {Γ ∪ {(x', A)} ∪ {(x, B)}} P) →
      -----------------------------------------------------------
      TypingStep (Typing.parr 𝒟) (Lbl.act (Act.parr x x')) 𝒟

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'} {ℰ : Typing ℋ Q} :
      TypingStep 𝒟 l 𝒟' → (l.iNames) ∩ (Q.fNames) = ∅ →
      --------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'} :
      TypingStep ℰ l ℰ' → (l.iNames) ∩ (P.fNames) = ∅ →
      --------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {a a' : Act}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'}
      {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'} :
      (h₁ : TypingStep 𝒟 a 𝒟') → TypingStep ℰ a' ℰ' →
      ((Lbl.par a a').iNames ∩ (Proc.par P Q).fNames) = ∅ →
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) (Lbl.par a a') (Typing.mix 𝒟' ℰ')

  | alpha_equiv
      {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing 𝒢 Q} {ℰ' : Typing 𝒢' Q'} :
      AlphaEq P Q → TypingStep ℰ l ℰ' →
      --------------------------------------------------------
      TypingStep 𝒟 l ℰ'

  | one_bot
      {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
      {𝒟 : Typing (𝒢 ∪ {{(x, Types.one)}} ∪ {Γ ∪ {(y, Types.bot)}}) P}
      {𝒟' : Typing (𝒢 ∪ {Γ}) P'} :
      TypingStep 𝒟 (Lbl.par (Act.one x) (Act.bot y)) 𝒟' →
      -----------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 ∅ Γ P x y (Types.one) 𝒟) (Lbl.tau) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
      {𝒟 : Typing (𝒢 ∪ {(Γ ∪ Δ) ∪ {(x, Types.tensor A B)}} ∪
        {Ξ ∪ {(y, Types.parr A.dual B.dual)}}) P
      }
      {𝒟' : Typing ((𝒢 ∪ {Γ ∪ {(x, B)}}) ∪ {Δ ∪
        {(x', A)}} ∪ {(Ξ ∪ {(y, B.dual)}) ∪ {(y', A.dual)}}) P'
      } :
      TypingStep 𝒟 (Lbl.par (Act.tensor x x') (Act.parr y y')) 𝒟' →
      ----------------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 (Γ ∪ Δ) Ξ P x y (Types.tensor A B) 𝒟)
        (Lbl.tau)
        (by constructor
          -- let inner := Typing.cut (𝒢 ∪ {Γ ∪ {(x, B)}}) Δ (Ξ ∪ {(y, B.dual)}) P' x' y' A 𝒟'
          -- conv at inner => lhs ; rhs ; rhs ; rw [← Env.merge_assoc]
          -- exact Typing.cut 𝒢 Γ (Δ ∪ Ξ) (Proc.cut x' y' P') x y B inner
        )

  | res
      {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
      {x y : PName} {A : Types} {l : Lbl}
      {𝒟 : Typing (𝒢 ∪ {Γ ∪ {(x, A)}} ∪ {Δ ∪ {(y, A.dual)}}) P}
      {𝒟' : Typing (𝒢' ∪ {Γ' ∪ {(x, A)}} ∪ {Δ' ∪ {(y, A.dual)}}) P'}
      (h : TypingStep 𝒟 l 𝒟')
      (disj : l.fresh [x, y]) :
      ----------------------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')







example {Γ : Env} {P : Proc} {x y : PName}
  (ℱ : Typing {Γ ∪ {(x, (Types.parr Types.bot Types.bot))}} (Proc.parr x y P))
  (ℱ' : Typing {Γ ∪ {(y, Types.bot)} ∪ {(x, Types.bot)}} P) :
  TypingStep ℱ (Lbl.act (Act.parr x y)) ℱ' := by
  apply TypingStep.parr

theorem ℰ (Γ Γ' : Env) (x x' : PName) (A B : Types) (Q : Proc)
  (ℰ' : Typing ({Γ' ∪ {(x', A)}} ∪ {Γ ∪ {(x, B)}}) Q) :
  Typing {Γ' ∪ Γ ∪ {(x, Types.tensor A B)}} (Proc.tensor x x' Q) := by
  apply Typing.tensor
  exact ℰ'

theorem ℱ (Δ : Env) (R : Proc) (y y' z : PName) (A B : Types)
  (ℱ' : Typing {Δ ∪ {(y', A.dual)} ∪ {(y, B.dual)}} R) :
  Typing
    {Δ ∪ {(y, Types.parr A.dual B.dual)} ∪ {(z, Types.bot)}}
    (Proc.parr y y' (Proc.bot z R)) := by
  rw [Env.merge_swap_last]
  apply Typing.parr
  rw [Env.merge_assoc, Env.merge_swap_last]
  apply Typing.bot
  rw [← Env.merge_assoc]
  exact ℱ'

theorem 𝒟 (Γ Γ' Δ : Env) (Q R : Proc) (x x' y y' z) (A B : Types)
  (ℰ' : Typing ({Γ' ∪ {(x', A)}} ∪ {Γ ∪ {(x, B)}}) Q)
  (ℱ' : Typing {Δ ∪ {(y', A.dual)} ∪ {(y, B.dual)}} R) :
  Typing
    {Γ' ∪ Γ ∪ Δ ∪ {(z, Types.bot)}}
    (Proc.cut x y (Proc.par (Proc.tensor x x' Q) (Proc.parr y y' (Proc.bot z R)))) := by
    let t := Typing.cut ∅ (Γ' ∪ Γ) (Δ ∪ {(z, Types.bot)})
      (Proc.par (Proc.tensor x x' Q) (Proc.parr y y' (Proc.bot z R))) x y (Types.tensor A B)
    repeat rw [HyperEnv.merge_unitL] at t
    rw [Env.merge_assoc]
    apply t
    apply Typing.mix
    · apply Typing.tensor
      exact ℰ'
    · apply Typing.parr
      rw [Env.merge_assoc, Env.merge_swap_last]
      apply Typing.bot
      rw [← Env.merge_assoc]
      exact ℱ'
