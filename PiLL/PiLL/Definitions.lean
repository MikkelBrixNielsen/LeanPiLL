----------------------------------------- imports -----------------------------------------
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Lean.PrettyPrinter.Delaborator
import Mathlib.Tactic

------------------------------------------ TYPES  ------------------------------------------

abbrev Atom := Nat
abbrev TVar := Nat

inductive Types : Type where
  | atom      (a : Atom)                -- named type, like A, B, ...
  | atomDual  (a : Atom)                -- dual of a named type
  | var       (v : TVar)                -- type variable
  | varDual   (v : TVar)                -- dual type variables
  | one                                 -- 𝟙 (empty output, unit for ⊗)
  | bot                                 -- ⊥ (empty send, unit for ⅋)
  | zero                                -- 𝟘 (unit for ⊕)
  | top                                 -- ⊤ (unit for &)
  | tensor    (A B : Types)             -- A ⊗ B (send)
  | parr      (A B : Types)             -- A ⅋ B (receive)
  | oplus     (A B : Types)             -- A ⊕ B (select A or B)
  | amp       (A B : Types)             -- A & B (Offer A or B)
  | bang      (A : Types)               -- !A (server accept)
  | quest     (A : Types)               -- ?A (client request)
  | forall_   (v : TVar) (A : Types)    -- ∀X.A (universal type input)
  | exist_    (v : TVar) (A : Types)    -- ∃X.A (existential type output)
deriving DecidableEq, BEq

infixr:90 " ⊗ " => Types.tensor
infixr:90 " ⊕ " => Types.oplus
infixr:90 " ⅋ " => Types.parr
infixr:90 " & " => Types.amp

instance : Zero Types := ⟨Types.zero⟩
instance : One Types := ⟨Types.one⟩
instance : Top Types := ⟨Types.top⟩
instance : Bot Types := ⟨Types.bot⟩

prefix:max "?ₜ" => Types.quest
prefix:max "!ₜ" => Types.bang

notation:90 "∃⸨" v "⸩." A => Types.exist_ v A
notation:90 "∀⸨" v "⸩." A => Types.forall_ v A

private def reprTypesAux : Types → Nat → String
  | .atom a, _ => s!"A{a}"
  | .atomDual a, _ => s!"A{a}ᗮ"
  | .var v, _ => s!"V{v}"
  | .varDual v, _ => s!"V{v}ᗮ"
  | .one, _ => "1"
  | .bot, _ => "⊥"
  | .zero, _ => "0" -- FIXME: Probably don't need
  | .top, _ => "⊤"  -- FIXME: Probably don't need
  | .tensor A B, _ => s!"({reprTypesAux A 0} ⊗ {reprTypesAux B 0})"
  | .parr A B, _ => s!"({reprTypesAux A 0} ⅋ {reprTypesAux B 0})"
  | .oplus A B, _ => s!"({reprTypesAux A 0} ⊕ {reprTypesAux B 0})"
  | .amp A B, _ => s!"({reprTypesAux A 0} & {reprTypesAux B 0})"
  | .bang A, _ => s!"!ₜ{reprTypesAux A 0}"
  | .quest A, _ => s!"?ₜ{reprTypesAux A 0}"
  | .forall_ v A, _ => s!"∀⸨{v}⸩.{reprTypesAux A 0}"
  | .exist_ v A, _ => s!"∃⸨{v}⸩.{reprTypesAux A 0}"

instance : Repr Types where
  reprPrec A _ := reprTypesAux A 0

instance : ToString Types where
  toString t := reprStr t

def Types.pos : Types → Prop
  | .atom _ => True
  | .var _ => True
  | .one => True
  | .zero => True
  | .tensor _ _ => True
  | .oplus _ _ => True
  | .bang _ => True
  | .exist_ _ _ => True
  | _ => False

def Types.neg : Types → Prop
  | .atomDual _ => True
  | .varDual _ => True
  | .bot => True
  | .top => True
  | .parr _ _ => True
  | .amp _ _ => True
  | .quest _ => True
  | .forall_ _ _ => True
  | _ => False

instance Types.positive_decidable (A : Types) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negative_decidable (A : Types) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

@[simp]
def Types.dual : Types → Types
  | .atom a       => .atomDual a
  | .atomDual a   => .atom a
  | .var v        => .varDual v
  | .varDual v    => .var v
  | .one          => .bot
  | .bot          => .one
  | .zero         => .top
  | .top          => .zero
  | .tensor A B   => .parr (dual A) (dual B)
  | .parr A B     => .tensor (dual A) (dual B)
  | .oplus A B    => .amp (dual A) (dual B)
  | .amp A B      => .oplus (dual A) (dual B)
  | .bang A       => .quest (dual A)
  | .quest A      => .bang (dual A)
  | .forall_ v A  => .exist_ v (dual A)
  | .exist_ v A   => .forall_ v (dual A)

notation:max A "ᗮ" => Types.dual A

@[simp]
theorem Types.dual_neq (A : Types) : A ≠ Aᗮ := by
  cases A <;> simp [dual]

@[simp]
theorem Types.dual_inj (A B : Types) : Aᗮ = Bᗮ ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem Types.dual_involution (A : Types) : Aᗮᗮ = A := by
  induction A <;> simp [*]

def Types.linImpl (A B : Types) : Types := Aᗮ ⅋ B
infix:90 " ⊸ " => Types.linImpl

def Types.freeTypes : Types → Finset TVar
  | .atom _ | .atomDual _ | .one | .bot | .zero | .top => ∅
  | .var v        => {v}
  | .varDual v    => {v}
  | .tensor A B   => A.freeTypes ∪ B.freeTypes
  | .parr A B     => A.freeTypes ∪ B.freeTypes
  | .oplus A B    => A.freeTypes ∪ B.freeTypes
  | .amp A B      => A.freeTypes ∪ B.freeTypes
  | .bang A       => A.freeTypes
  | .quest A      => A.freeTypes
  | .forall_ v A  => A.freeTypes \ {v}
  | .exist_ v A   => A.freeTypes \ {v}

def Types.subst (T R : Types) (X : TVar) : Types :=
  match T with
  | .atom a => .atom a
  | .atomDual a => .atomDual a
  | .var v => if v = X then R else .var v
  | .varDual v => if v = X then Rᗮ else .varDual v
  | .one => .one
  | .bot => .one
  | .zero => .top
  | .top => .zero
  | .tensor A B => .tensor (A.subst R X) (B.subst R X)
  | .parr A B => .parr (A.subst R X) (B.subst R X)
  | .oplus A B => .oplus (A.subst R X) (B.subst R X)
  | .amp A B => .amp (A.subst R X) (B.subst R X)
  | .bang A       => .bang (A.subst R X)
  | .quest A      => .quest (A.subst R X)
  -- FIXME: This does not avoud capture if B includes v
  | .forall_ v A  => if v = X then .forall_ v A else .forall_ v (A.subst R X)
  | .exist_ v A  => if v = X then .exist_ v A else .exist_ v (A.subst R X)

notation:88 T "{" R " // " X "}" => Types.subst T R X

------------------------------------------ Proc  ------------------------------------------

abbrev PName := Nat -- Process names are just numbers (ensures not empty)

inductive Proc : Type where
  | tensor    (x y : PName) (P : Proc)            -- x[y].P
  | parr      (x y : PName) (P : Proc)            -- x(y).P
  | one       (x : PName) (P : Proc)              -- x[].P
  | bot       (x : PName) (P : Proc)              -- x().P
  | cut       (x y : PName) (P : Proc)            -- 𝒗xy P
  | par       (P Q : Proc)                        -- P | Q
  | nil                                           -- 𝟘
  | selectL   (x : PName) (P : Proc)              -- x[L].P
  | selectR   (x : PName) (P : Proc)              -- x[R].P
  | offer     (x : PName) (P Q : Proc)            -- x.case{L : P, R : Q}
  | output    (x : PName) (P : Proc) (A : Types)  -- x[A].P
  | input     (x : PName) (P : Proc) (X : TVar)   -- x(X).P
  | server    (x : PName) (P : Proc)              -- !x.{P}
  | consume   (x : PName) (P : Proc)              -- x[USE].P
  | duplicate (x y : PName) (P : Proc)            -- x[DUP](y).P
  | dispose   (x : PName) (P : Proc)              -- x[DISP].P
  | link      (x y : PName)                       -- x ⟷ y
deriving DecidableEq

notation:80 x "⟦" y "⟧." P:80 => Proc.tensor x y P
notation:80 x "⟦⟧." P:80 => Proc.one x P
notation:80 x "⸨" y "⸩." P:80 => Proc.parr x y P
notation:80 x "⸨⸩." P:80 => Proc.bot x P
notation:75 "𝑣" "⸨" x ", " y "⸩ " P => Proc.cut x y P

notation:80 x "⟦𝐋⟧." P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧." P:80 => Proc.selectR x P
notation:80 "⸨" x "⸩.case⦃𝐋" " : " P:80 ", " "𝐑" " : " Q :80"⦄" => Proc.offer x P Q
notation:80 x "⟦" A "⟧:" P => Proc.output x P A
notation:80 x "⸨" X "⸩:" P => Proc.input x P X
notation:80 "!" x ".⦃" P "⦄" => Proc.server x P
notation:80 x "⟦USE⟧." P => Proc.consume x P
notation:80 x "⟦DUP⟧⸨" y "⸩." P => Proc.duplicate x y P
notation:80 x "⟦DISP⟧." P => Proc.dispose x P
notation:80 x "⟷ₚ" y => Proc.link x y

notation "𝟘" => Proc.nil
infixr:70 " |ₚ " => Proc.par

private def reprProcAux : Proc → Nat → String
  | .nil, _ => "𝟘"
  | .tensor x y P, _ => s!"{x}⟦{y}⟧.{reprProcAux P 0}"
  | .one x P, _ => s!"{x}⟦⟧.{reprProcAux P 0}"
  | .parr x y P, _ => s!"{x}⸨{y}⸩.{reprProcAux P 0}"
  | .bot x P, _ => s!"{x}⸨⸩.{reprProcAux P 0}"
  | .cut x y P, _ => s!"𝑣⸨{x}, {y}⸩ {reprProcAux P 0}"
  | .par P Q, _ => s!"({reprProcAux P 0} |ₚ {reprProcAux Q 0})"
  | .selectL x P, _ => s!"{x}⟦𝐋⟧.{reprProcAux P 0}"
  | .selectR x P, _ => s!"{x}⟦𝐑⟧.{reprProcAux P 0}"
  | .offer x P Q, _ => s!"⸨{x}⸩.case⦃𝐋 : {reprProcAux P 0}, 𝐑 : {reprProcAux Q 0}⦄"
  | .output x P A, _ => s!"{x}⟦{A}⟧.{reprProcAux P 0}"
  | .input x P X, _ => s!"{x}⟦{X}⟧.{reprProcAux P 0}"
  | .server x P, _ => s!"!{x}.⦃{reprProcAux P 0}⦄"
  | .consume x P, _ => s!"{x}⟦USE⟧.{reprProcAux P 0}"
  | .duplicate x y P, _ => s!"{x}⟦DUP⟧⸨{y}⸩.{reprProcAux P 0}"
  | .dispose x P, _ => s!"{x}⟦DISP⟧.{reprProcAux P 0}"
  | .link x y, _ => s!"{x}⟷{y}"

instance : Repr Proc where
  reprPrec P _ := reprProcAux P 0

instance : ToString Proc where
  toString p := reprStr p

@[simp]
def Proc.f : Proc → Finset PName
  | .tensor x y P         => {x} ∪ (P.f \ {y})
  | .parr x y P           => {x} ∪ (P.f \ {y})
  | .one x P              => {x} ∪ P.f
  | .bot x P              => {x} ∪ P.f
  | .cut x y P            => P.f \ {x, y}
  | .par P Q              => P.f ∪ Q.f
  | .nil                  => {}
  | .selectL x P          => {x} ∪ P.f
  | .selectR x P          => {x} ∪ P.f
  | .offer x P Q          => {x} ∪ (P.f ∪ Q.f)
  | .output x P _         => {x} ∪ P.f
  | .input  x P _         => {x} ∪ P.f
  | .server x P           => {x} ∪ P.f
  | .consume x P          => {x} ∪ P.f
  | .duplicate x y P      => {x} ∪ (P.f \ {y})
  | .dispose x P          => {x} ∪ P.f
  | .link x y             => {x, y}

@[simp]
def Proc.names : Proc → Finset PName
  | .tensor x y P         => {x, y} ∪ P.names
  | .parr x y P           => {x, y} ∪ P.names
  | .one x P              => {x} ∪ P.names
  | .bot x P              => {x} ∪ P.names
  | .cut x y P            => {x, y} ∪ P.names
  | .par P Q              => P.names ∪ Q.names
  | .nil                  => {}
  | .selectL x P          => {x} ∪ P.names
  | .selectR x P          => {x} ∪ P.names
  | .offer x P Q          => {x} ∪ (P.names ∪ Q.names)
  | .output x P _         => {x} ∪ P.names
  | .input  x P _         => {x} ∪ P.names
  | .server x P           => {x} ∪ P.names
  | .consume x P          => {x} ∪ P.names
  | .duplicate x y P      => {x, y} ∪ P.names
  | .dispose x P          => {x} ∪ P.names
  | .link x y             => {x, y}

abbrev Renaming := PName → PName

def rename (ρ : Renaming) : Proc → Proc
  | .tensor x y P     => .tensor (ρ x) (ρ y) (rename ρ P)
  | .parr x y P       => .parr (ρ x) (ρ y) (rename ρ P)
  | .one x P          => .one (ρ x) (rename ρ P)
  | .bot x P          => .bot (ρ x) (rename ρ P)
  | .cut x y P        => .cut (ρ x) (ρ y) (rename ρ P)
  | .par P Q          => .par (rename ρ P) (rename ρ Q)
  | .nil              => .nil
  | .selectL x P      => .selectL (ρ x) (rename ρ P)
  | .selectR x P      => .selectR (ρ x) (rename ρ P)
  | .offer x P Q      => .offer (ρ x) (rename ρ P) (rename ρ Q)
  | .output x P A     => .output (ρ x) (rename ρ P) A
  | .input x P A      => .input (ρ x) (rename ρ P) A
  | .server x P       => .server (ρ x) (rename ρ P)
  | .consume x P      => .consume (ρ x) (rename ρ P)
  | .duplicate x y P  => .duplicate (ρ x) (ρ y) (rename ρ P)
  | .dispose x P      => .dispose (ρ x) (rename ρ P)
  | .link x y         => .link (ρ x) (ρ y)

def freshName (s : Finset Nat) : PName :=
  (Finset.fold Nat.max 0 id s) + 1

def renameBound old new P := rename (fun curr => if curr = old then new else curr) P

def renameBound2 old1 old2 new1 new2 P := renameBound old2 new2 (renameBound old1 new1 P)

-- Only bound names should be renamed and free names should match exactly
inductive AlphaEq : Proc → Proc → Prop where
  | nil : AlphaEq .nil .nil

  | par {P1 Q1 P2 Q2 : Proc} :
      AlphaEq P1 Q1 → AlphaEq P2 Q2 → AlphaEq (.par P1 P2) (.par Q1 Q2)

  | one {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.one x P) (.one x' Q)

  | tensor {P Q : Proc} {x y x' y' : PName} -- x, x' are free y, y' are bound
      (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
      AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
      AlphaEq (.tensor x y P) (.tensor x' y' Q)

  | bot {P Q : Proc} {x x' : PName} : -- Both PNames are free
      AlphaEq P Q → x = x' → AlphaEq (.bot x P) (.bot x' Q)

  | parr {P Q : Proc} {x y x' y' : PName} -- x x' are Free, y y' are bound
      (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
        AlphaEq (.parr x y P) (.parr x' y' Q)

  | cut {P Q : Proc} {x y x' y' : PName} -- x y x' y' are all bound
      (w1 w2 : PName) (hFresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ Q.names ∧ w2 ∉ P.names ∪ Q.names) :
        AlphaEq (renameBound2 x y w1 w2 P) (renameBound2 x' y' w1 w2 Q) →
        AlphaEq (.cut x y P) (.cut x' y' Q)

  | selectL {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.selectL x P) (.selectL x' Q)

  | selectR {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.selectR x P) (.selectR x' Q)

  | offer {P1 Q1 P2 Q2 : Proc} {x x' : PName} :
      AlphaEq P1 P2 → AlphaEq Q1 Q2 → x = x' → AlphaEq (.offer x P1 Q1) (.offer x' P2 Q2)

  | output {P Q : Proc} {x x' : PName} {A A' : Types}:
      AlphaEq P Q → x = x' → A = A' → AlphaEq (.output x P A) (.output x' Q A')

  | input {P Q : Proc} {x x' : PName} {X X' : TVar} :
      AlphaEq P Q → x = x' → X = X' → AlphaEq (.input x P X) (.input x' Q X')

  | server {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.server x P) (.server x' Q)

  | consume {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.consume x P) (.consume x' Q)

  | duplicate {P Q : Proc} {x y x' y' : PName} :
      AlphaEq P Q → x = x' → y = y' → AlphaEq (.duplicate x y P) (.duplicate x' y' Q)

  | dispose {P Q : Proc} {x x' : PName} :
      AlphaEq P Q → x = x' → AlphaEq (.dispose x P) (.dispose x' Q)

  | link {x y x' y' : PName} :
      x = x' → y = y' → AlphaEq (.link x y) (.link x' y')

notation:60 P " =ₐ " Q => AlphaEq P Q

def Proc.size : Proc → Nat
| .nil => 1
| .link _ _ => 1
| .par P Q => 1 + P.size + Q.size
| .offer _ P Q => 1 + P.size + Q.size
| .tensor _ _ P | .parr _ _ P | .one _ P | .bot _ P | .cut _ _ P | .selectL _ P
| .selectR _ P | .output _ P _ | .input _ P _ | .server _ P | .consume _ P
| .dispose _ P | .duplicate _ _ P => 1 + P.size

lemma freshName_is_fresh (s : Finset PName) : freshName s ∉ s := by
  let m := Finset.fold Nat.max 0 id s
  have h_max : ∀ n ∈ s, n ≤ m := by
    intro n hn ; rw [Finset.le_fold_max] ; grind
  intro h_contra
  specialize h_max (freshName s) h_contra
  unfold m freshName at h_max
  apply Nat.not_succ_le_self (Finset.fold Nat.max 0 id s)
  exact h_max

lemma size_renameBound_eq (old new : PName) (P : Proc) :
  (renameBound old new P).size = P.size := by
  induction P
  case nil | link =>
    simp [renameBound, Proc.size]
    apply rfl
  case one P ih | bot P ih | selectL P ih | selectR P ih | server P ih
    | consume P ih | duplicate P ih | dispose P ih =>
    simp [renameBound, rename, Proc.size]
    unfold renameBound at ih
    apply ih
  case input P A ih | output P X ih | tensor P ih | parr P ih | cut P ih =>
    simp [renameBound, rename, Proc.size]
    simp [renameBound] at ih
    rw [ih]
  case par P Q ihP ihQ | offer P Q ihP ihQ =>
    simp [renameBound, rename, Proc.size]
    simp [renameBound] at ihP
    simp [renameBound] at ihQ
    rw [ihP, ihQ]

@[refl]
theorem AlphaEq.refl (P : Proc) : P =ₐ P := by
  induction h : P.size using Nat.strong_induction_on generalizing P
  rename_i n ih
  cases P

  case nil | link => repeat constructor

  case par P Q =>
    constructor
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
        omega
      · rfl
    · apply ih Q.size
      · rw [← h]
        simp [Proc.size]
      · rfl

  case tensor x y P | parr x y P =>
    constructor
    · simp ; exact freshName_is_fresh P.names
    · apply ih P.size
      · rw [← h]
        simp only [Proc.size]
        omega
      · simp [size_renameBound_eq]
    · rfl

  case cut x y P =>
    let w1 := freshName P.names
    let w2 := freshName (P.names ∪ {w1})
    have h_fresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ P.names ∧ w2 ∉ P.names ∪ P.names := by
      constructor
      · intro h_eq ; unfold w1 at h_eq ; unfold w2 at h_eq
        exact absurd (freshName_is_fresh (P.names ∪ {w1})) (by grind)
      · simp
        apply And.intro
        · exact freshName_is_fresh P.names
        · unfold w2 w1
          · intro h_contra
            apply freshName_is_fresh (P.names ∪ {freshName P.names})
            apply Finset.mem_union_left
            exact h_contra
    apply AlphaEq.cut
    · exact h_fresh
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
      · unfold renameBound2
        simp [size_renameBound_eq]

  case one _ P | bot _ P | selectL _ P | selectR _ P | server _ P | dispose _ P
    | consume _ P | duplicate _ _ P | output _ P _ | input _ P _ =>
    constructor
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
      · rfl
    repeat rfl

  case offer _ P Q =>
    apply AlphaEq.offer
    · apply ih P.size
      · rw [← h]
        simp [Proc.size]
        omega
      · rfl
    · apply ih Q.size
      · rw [← h]
        simp [Proc.size]
      · rfl
    · rfl

theorem AlphaEq.symm (P Q : Proc) (h : P =ₐ Q) : (Q =ₐ P) := by
  induction h
  case nil => rfl
  case one | bot | par | selectL | selectR | offer | output | input | server
    | consume | duplicate | dispose | link => constructor ; repeat simp [*]

  case tensor _ _ _ _ _ _ _ hwnPQ _ hxxp hrbQP
    | parr tensor _ _ _ _ _ _ hwnPQ _ hxxp hrbQP =>
    constructor
    · rw [Finset.union_comm] ; exact hwnPQ
    · exact hrbQP
    · rw [Eq.comm] ; exact hxxp

  case cut _ _ _ _ _ _ _ _ h_fresh hrbPQ hrbQP =>
    constructor
    · rw [Finset.union_comm] ; exact h_fresh
    · exact hrbQP

theorem AlphaEq.comm (P Q : Proc) : (P =ₐ Q) = (Q =ₐ P) := by
  apply propext
  constructor
  · apply AlphaEq.symm
  · apply AlphaEq.symm

-- lemma renameBound_comm {x y a b : PName} {P : Proc} :
--   (hxy : x ≠ y) → (hab : a ≠ b) → (hxb : x ≠ b) → (hya : y ≠ a) →
--   renameBound x a (renameBound y b P) = renameBound y b (renameBound x a P) := by
--   intros
--   induction P <;> simp [renameBound, rename, *]
--   case one ih | bot ih | selectL ih | selectR ih | output ih | input ih
--     | server ih | consume ih | dispose ih =>
--     apply And.intro
--     · aesop
--     · exact ih

--   case par P_ih Q_ih =>
--     apply And.intro
--     · exact P_ih
--     · exact Q_ih

--   case offer P_ih Q_ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · exact P_ih
--       · exact Q_ih

--   case link =>
--     apply And.intro
--     · aesop
--     · aesop

--   case tensor ih | parr ih | cut ih | duplicate ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · aesop
--       · exact ih

-- lemma renameBound_commutes (a b : PName) (P : Proc) (ha : a ∉ P.names) (hb : b ∉ P.names) :
--   renameBound a b P = P := by
--   induction P generalizing a b
--   all_goals simp [rename, renameBound, *]

--   case tensor x y P ih | parr x y P ih | cut x y P ih | duplicate x y P ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · intro h ; simp_all
--       · apply ih <;> simp_all

--   case one x P ih | bot x P ih | selectL x P ih | selectR x P ih | server x P ih
--     | consume x P ih | dispose x P ih | output x P A ih | input x P X ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply ih <;> simp_all

--   case offer x P Q ihP ihQ =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · apply ihP <;> simp_all
--       · apply ihQ <;> simp_all

--   case par P Q ihP ihQ =>
--     apply And.intro
--     · apply ihP <;> simp_all
--     · apply ihQ <;> simp_all

--   case link =>
--     apply And.intro
--     · intro h ; simp_all
--     · intro h ; simp_all


-- lemma renameBound_comp (x y z : PName) (P : Proc) (hx : x ∉ P.names) (hxy : x ≠ y) :
--   renameBound x z (renameBound y x P) = renameBound y z P := by
--   induction P generalizing x y z <;> simp [renameBound, rename, *] at *
--   all_goals aesop

-- theorem AlphaEq_swap_fresh (y y' w1 w2 : PName) (P Q : Proc)
--   (hFresh1 : w1 ∉ P.names ∪ Q.names)
--   (hFresh2 : w2 ∉ P.names ∪ Q.names)
--   (h : renameBound y w1 P =ₐ renameBound y' w1 Q) :
--   (renameBound y w2 P =ₐ renameBound y' w2 Q) := by sorry

theorem AlphaEq.trans (P Q R : Proc) (hPQ : P =ₐ Q) (hQR : Q =ₐ R) : P =ₐ R := by sorry
--   induction P.size + Q.size using Nat.strong_induction_on generalizing P Q R
--   rename_i n ih
--   cases hPQ <;> cases hQR
--   case nil.nil => rfl
--   case par.par =>
--     rename_i P1 Q1 P2 Q2 h1 h2 Q1' Q2' h5 h6
--     apply AlphaEq.par
--     · sorry

def Proc.substType (P : Proc) (A : Types) (X : TVar) : Proc :=
  match P with
  | .nil => .nil
  | .one x P => .one x (P.substType A X)
  | .bot x P => .bot x (P.substType A X)
  | .tensor x y P => .tensor x y (P.substType A X)
  | .parr x y P => .parr x y (P.substType A X)
  | .cut x y P => .cut x y (P.substType A X)
  | .par P Q => .par (P.substType A X) (Q.substType A X)
  | .selectL x P => .selectL x (P.substType A X)
  | .selectR x P => .selectR x (P.substType A X)
  | .offer x P Q => .offer x (P.substType A X) (Q.substType A X)
  | .server x P => .server x (P.substType A X)
  | .dispose x P => .dispose x (P.substType A X)
  | .duplicate x y P => .duplicate x y (P.substType A X)
  | .consume x P => .consume x (P.substType A X)
  | .link x y => .link x y
  | .output x P B => .output x (P.substType A X) (B.subst A X)
  | .input x P Y => if Y = X then .input x P Y else .input x (P.substType A X) Y

notation:65 P"⦃" A "//" X "⦄ₜ" => Proc.substType P A X

def Proc.substName (P : Proc) (x z : PName) : Proc :=
  let sub := fun (c : PName) => if c = z then x else c
  match P with
  | .nil => .nil
  | .one a P => .one (sub a) (P.substName x z)
  | .bot a P => .bot (sub a) (P.substName x z)
  | .tensor a b P =>
      if b = z then .tensor (sub a) b P
      else .tensor (sub a) b (P.substName x z)
  | .parr a b P =>
      if b = z then .parr (sub a) b P
      else .parr (sub a) b (P.substName x z)
  | .cut a b P =>
      if a = z ∨ b = z then .cut (sub a) (sub b) P
      else .cut (sub a) (sub b) (P.substName x z)
  | .par P Q => .par (P.substName x z) (Q.substName x z)
  | .selectL a P => .selectL (sub a) (P.substName x z)
  | .selectR a P => .selectR (sub a) (P.substName x z)
  | .offer a P Q => .offer (sub a) (P.substName x z) (Q.substName x z)
  | .server a P => .server (sub a) (P.substName x z)
  | .dispose a P => .dispose (sub a) (P.substName x z)
  | .duplicate a b P =>
      if b = z then .duplicate (sub a) (sub b) P
      else .duplicate (sub a) (sub b) (P.substName x z)
  | .consume a P => .consume (sub a) (P.substName x z)
  | .link a b => .link (sub a) (sub b)
  | .output a P A => .output (sub a) (P.substName x z) A
  | .input a P X => .input (sub a) (P.substName x z) X

notation:65 P"⦃" x "//" z "⦄ₙ" => Proc.substName P x z

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

infixr:86 " ∶ " => Env.mk

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

@[simp]
def Env.merge (Δ Γ : Env) : Env := Δ ∪ Γ

infixl:85 "‚ " => Env.merge

-- Merge identity
@[simp]
theorem Env.merge_unitR (Δ : Env) : Δ‚ ∅ = Δ := by
  simp

@[simp]
theorem Env.merge_unitL (Δ : Env) : ∅‚ Δ = Δ := by
  simp

-- Merge commutivity
-- theorem mergeEnv.comm (Δ Γ : Env) : disjointEnv Δ Γ → mergeEnv Δ Γ = mergeEnv Γ Δ := by
@[simp]
theorem Env.merge_comm (Δ Γ : Env) : Δ‚ Γ = Γ‚ Δ := by
  simp [Finset.union_comm]

-- Merge associativity
@[simp]
theorem Env.merge_assoc (Δ Γ Ε : Env) : Δ‚ Γ‚ Ε = Δ‚ (Γ‚ Ε) := by
  simp

@[simp]
lemma Env.merge_swap_last (Γ Δ Ξ : Env) :
  (Γ‚ Δ)‚ Ξ = (Γ‚ Ξ)‚ Δ := by
  rw [Env.merge_comm, ←Env.merge_assoc]
  conv => lhs ; lhs ; rw [Env.merge_comm]

@[simp]
lemma Env.merge_move_last_two_left (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ε‚ Δ‚ Ξ := by
  rw [Env.merge_swap_last, Env.merge_swap_last Γ Δ Ε]

@[simp]
lemma Env.merge_move_second_two_right (Γ Δ Ξ Ε : Env) :
  Γ‚ Δ‚ Ξ‚ Ε = Γ‚ Ξ‚ Ε‚ Δ := by
  rw [Env.merge_swap_last Γ Δ Ξ, Env.merge_swap_last]

def isServerUsable : Types → Prop
  | .quest _  => True
  | .bang _   => True
  | _         => False

def serverUsableEnv (Γ : Env) : Prop :=
  ∀p, p ∈ Γ → isServerUsable p.snd = True

prefix:max "?ₑ" => serverUsableEnv

def Env.freeTypes (Γ : Env) : Finset TVar :=
  Γ.biUnion (fun (_, A) => A.freeTypes)

notation "ft(" Γ ")" => Env.freeTypes Γ

------------------------------------ HYPER-ENVIRONMENTS ------------------------------------

abbrev HyperEnv := Finset (Env)

abbrev EmptyHyperEnv : HyperEnv := ∅

instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

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

infixl:55 " |ₕ " => HyperEnv.merge

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
      Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
      -----------------------------------------
      Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types} :
      Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
      ------------------------------------
      Typing (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦y⟧.P)

  | one {P : Proc} {x : PName} :
      Typing ∅ P →
      ----------------------
      Typing (x ∶ 1) (x⟦⟧.P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
      Typing (Γ‚ y ∶ A‚ x ∶ B) P →
      --------------------------------
      Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩.P)

  | bot {Γ : Env} {P : Proc} {x : PName} :
      Typing Γ P →
      --------------------------
      Typing (Γ‚ x ∶ ⊥) (x⸨⸩.P)

  | oplus₁
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧.P)

  | oplus₂
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ B) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧.P)

  | amp
      {Γ : Env} {P Q : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P → Typing (Γ‚ x ∶ B) Q →
      ---------------------------------------------
      Typing (Γ‚ x ∶ A & B) (⸨x⸩.case⦃𝐋 : P, 𝐑 : Q⦄)

  | quest
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P →
      -----------------------------
      Typing (Γ‚ x ∶ ?ₜA) (x⟦USE⟧.P)

  | w
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing Γ P →
      -----------------------------
      Typing (Γ‚ x ∶ ?ₜA) (x⟦DISP⟧.P)

  | c
      {Γ : Env} {P : Proc} {x x' : PName} {A : Types} :
      Typing (Γ‚ x ∶ ?ₜA‚ x' ∶ ?ₜA) P →
      --------------------------------
      Typing (Γ‚ x ∶ ?ₜA) (x⟦DUP⟧⸨x'⸩.P)

  | bang
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P → ?ₑΓ →
      ------------------------------
      Typing (Γ‚ x ∶ !ₜA) (!x.⦃P⦄)

  -- | exists_ -- FIXME: Need replacement syntax defined
  --     {Γ : Env} {P : Proc} {x : PName} {A : Types} :
  --     Typing (Γ‚ x ∶ B{A / X}) P →
  --     --------------------------
  --     Typing (Γ‚ x ∶ ∃⸨X⸩.B) (x⟦A⟧:P)

  -- | forall_ -- FIXME: How to define Type variable X? And ft does not exist
  --     {Γ : Env} {P : Proc} {x : PName} {A : Types} : -- {X : Types.var} :
  --     Typing (Γ‚ x ∶ A) P → -- X ∉ Γ.fTypes →
  --     Typing (Γ‚ x ∶ ∀⸨X⸩.A) (x⸨X⸩:P)

  | ax
      {x y : PName} {A : Types} :
      Typing (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₚ y)

notation:50 "⊢ " P " ∷ " T => Typing T P

------------------------------------------ LABELS ------------------------------------------

inductive Mu : Type
  | L
  | R
  | DISP
  | DUP
  | USE
  | A (t : Types)
deriving Repr, DecidableEq

inductive Act : Type
  | one       (x : PName)               -- x[]
  | bot       (x : PName)               -- x()
  | tensor    (x y : PName)             -- x[y]
  | parr      (x y : PName)             -- x(y)
  | output    (x : PName) (A : Types)   -- x[A]
  | input     (x : PName) (A : Types)   -- x(A)
  | muBrack   (x : PName) (μ : Mu)      -- x[μ]
  | muParen   (x : PName) (μ : Mu)      -- x[μ]
deriving Repr, DecidableEq

@[simp]
def fNamesAct : Act -> Finset PName -- free names
  | .one x | .bot x
  | .tensor x _ | .parr x _
  | .input x _ | .output x _
  | .muBrack x _  | .muParen x _ => {x}

@[simp]
def iNamesAct : Act → Finset PName -- introduced names
  | .one _ | .bot _ | .input _ _ | .output _ _
  | Act.muBrack _ _ | Act.muParen _ _ => ∅
  | .tensor _ y | .parr _ y => {y}

inductive Lbl : Type
  | tau                   -- τ
  | link  (x y : PName)   -- x ⟷ y
  | act   (p : Act)       -- l, for l ∈ Act
  | par   (l l' : Act)    -- l | l' for l, l' ∈ Act, i(l) ∩ i(l') = ∅ (.WF)
deriving Repr, DecidableEq

abbrev Lbls := List Lbl

instance : Coe Act Lbl := ⟨Lbl.act⟩

@[simp]
def Lbl.WF : Lbl → Prop
  | .tau => True
  | .link _ _ => True
  | .act _ => True
  | .par l l' => (iNamesAct l) ∩ (iNamesAct l') = ∅

@[simp]
def Lbl.f : Lbl → Finset PName
  | .tau        => ∅
  | .link x y   => {x, y}
  | .act a      => fNamesAct a
  | .par l l'   => fNamesAct l ∪ fNamesAct l'

@[simp]
def Lbl.i : Lbl → Finset PName
  | .tau        => ∅
  | .link _ _   => ∅
  | .act a      => iNamesAct a
  | .par l l'   => iNamesAct l ∪ iNamesAct l'

@[simp]
def Lbl.fresh (xs : List PName) (l : Lbl) :=
  ∀ n ∈ xs, n ∉ l.f ∪ l.i

notation:80 x "⟦" y "⟧" => Act.tensor x y
notation:80 x "⟦⟧" => Act.one x
notation:80 x "⸨" y "⸩" => Act.parr x y
notation:80 x "⸨⸩" => Act.bot x
notation:80 "τ" => Lbl.tau
notation:80 x "⟷ₗ" y => Lbl.link x y
notation:70 l " |ₗ " l' => Lbl.par l l'
notation:80 x "⟦" A "⟧:" => Act.output x A
notation:80 x "⸨" A "⸩:" => Act.input x A

notation:80 x "⟦𝐋⟧" => Act.muBrack x Mu.L
notation:80 x "⸨𝐋⸩" => Act.muParen x Mu.L
notation:80 x "⟦𝐑⟧" => Act.muBrack x Mu.R
notation:80 x "⸨𝐑⸩" => Act.muParen x Mu.R
notation:80 x "⟦USE⟧" => Act.muBrack x Mu.USE
notation:80 x "⸨USE⸩" => Act.muParen x Mu.USE
notation:80 x "⟦DUP⟧" => Act.muBrack x Mu.DUP
notation:80 x "⸨DUP⸩" => Act.muParen x Mu.DUP
notation:80 x "⟦DISP⟧" => Act.muBrack x Mu.DISP
notation:80 x "⸨DISP⸩" => Act.muParen x Mu.DISP

notation:80 x "⟦" μ "⟧ₘ" => Act.muBrack x μ
notation:80 x "⸨" μ "⸩ₘ" => Act.muParen x μ

----------------------------- TRANSITION RULES FOR DERIVATIONS -----------------------------

inductive TypingStep : {𝒢 : HyperEnv} → {P : Proc} → Typing 𝒢 P →
  Lbl → {𝒢' : HyperEnv} → {P' : Proc} → Typing 𝒢' P' → Prop where
  | one
      {P : Proc} {x : PName} {𝒟 : Typing ∅ P} :
      TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
      {𝒟 : Typing (Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B) P} :
      TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : PName} {𝒟 : Typing {Γ} P} :
      TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

  | parr
      {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
      {𝒟 : Typing (Γ‚ x' ∶ A‚ x ∶ B) P} :
      TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'} {ℰ : Typing ℋ Q}
      (h : TypingStep 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h : TypingStep ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
      ---------------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act}
      {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'}
      {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
      (h₁ : TypingStep 𝒟 l 𝒟')
      (h₂ : TypingStep ℰ l' ℰ')
      (disj : (l |ₗ l').i ∩ (P |ₚ Q).f = ∅)
      (WF : (l |ₗ l').WF) : -- FIXME: Don't know how to show TypingStep preserves WF without this
      ---------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) (l |ₗ l') (Typing.mix 𝒟' ℰ')

  | alpha_equiv
      {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : Typing 𝒢 P} {ℰ : Typing 𝒢 Q} {ℰ' : Typing 𝒢' Q'}
      (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
      -------------------------------------------------------
      TypingStep 𝒟 l ℰ'

  | one_bot
      {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
      {𝒟 : Typing (𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥) P} {𝒟' : Typing (𝒢 |ₕ Γ) P'}
      (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
      ----------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 ∅ Γ P x y (1) 𝒟) (τ) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
      {𝒟 : Typing (𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⊗ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ) P}
      {𝒟' : Typing (𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ x' ∶ A |ₕ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ) P'}
      (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
      ----------------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒢 (Γ‚ Δ) Ξ P x y (A ⊗ B) 𝒟)
        (τ)
        (Typing.cut 𝒢 Γ (Δ‚ Ξ) (𝑣⸨x', y'⸩ P') x y B
          (by
           let inner := Typing.cut (𝒢 |ₕ {Γ‚ x ∶ B}) Δ (Ξ‚ y ∶ Bᗮ) P' x' y' A 𝒟'
           rw [← Env.merge_assoc] at inner
           exact inner
          )
        )

  | res
      {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
      {x y : PName} {A : Types} {l : Lbl}
      {𝒟 : Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P}
      {𝒟' : Typing (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ) P'}
      (h : TypingStep 𝒟 l 𝒟') (disj : l.fresh [x, y]) :
      ----------------------------------------------------------------------------
      TypingStep (Typing.cut 𝒢 Γ Δ P x y A 𝒟) l (Typing.cut 𝒢' Γ' Δ' P' x y A 𝒟')

notation:50 𝒟 " -[" l "]->ₜ " 𝒟' => TypingStep 𝒟 l 𝒟'

open Lean PrettyPrinter in
@[app_unexpander Lbl.act]
def unexpandLblAct : Unexpander
  | `($_ $a) => pure a
  | _ => pure Syntax.missing

theorem TypingStep.preserves_WF (Γ Γ' : HyperEnv) (P P' : Proc)
  (𝒟 : ⊢ P ∷ Γ) (𝒟' : ⊢ P' ∷ Γ') (l : Lbl) :
  TypingStep 𝒟 l 𝒟' → l.WF := by
  intro h
  induction h
  case one | bot | tensor | parr | one_bot | tensor_parr => simp [Lbl.WF]
  case par₁ | par₂| alpha_equiv | res => simp_all
  case syn WF ih1 ih2 => exact WF

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
      ProcStep P l P' → l.i ∩ Q.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P' |ₚ Q)

  | par₂
      {P Q Q' : Proc} {l : Lbl} :
      ProcStep Q l Q' → l.i ∩ P.f = ∅ →
      ----------------------------------
      ProcStep (P |ₚ Q) l (P |ₚ Q')

  | syn
      {P P' Q Q' : Proc} {l l' : Act} :
      ProcStep P l P' → ProcStep Q l' Q' →
      (l |ₗ l').i ∩ (P |ₚ Q).f = ∅  →
      -------------------------------------
      ProcStep (P |ₚ Q) (l |ₗ l') (P' |ₚ Q')

  | alpha_equiv
      {P Q Q' : Proc} {l : Lbl} :
      (P =ₐ Q) → ProcStep Q l Q' →
      -------------------------------
      ProcStep P l Q'

  | one_bot
      {P P' : Proc} {x y : PName} :
      ProcStep P (x⟦⟧ |ₗ y⸨⸩) P' →
      ----------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) P'

  | tensor_parr
      {P P' : Proc} {x x' y y' : PName} :
      ProcStep P (x⟦x'⟧ |ₗ y⸨y'⸩) P' →
      -------------------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ (𝑣⸨x', y'⸩ P'))

  | res
      {P P' : Proc} {x y : PName} {l : Lbl} :
      ProcStep P l P' → l.fresh [x, y] →
      -------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (l) (𝑣⸨x, y⸩ P')

  | dispose₁
      {P : Proc} {x : PName} :
      ProcStep (x⟦DISP⟧.P) (x⟦DISP⟧) (x⸨⸩.P)

  -- | disp₂ -- FIXME: how to define / produce z-set in premise and z processes in conclusion
  --     {P : Proc} {x x' z: PName} :
  --     P.f \ {x'} = {z, ..., zₙ} →
  --     ---------------------------------------------------------
  --     ProcStep (!x.{P}) (x⸨DISP⸩) (z₁⟦DISP⟧ ... zₙ⟦DISP⟧.x⟦⟧.𝟘)

  | dup₁
      {P : Proc} {x x' : PName} :
      ProcStep (x⟦DUP⟧⸨x'⸩.P) (x⟦DUP⟧) (x⸨x'⸩.P)

  -- | dup₂ -- FIXME: define sigma expansion, also needs z-set expansion
  --     {P Pσ : Proc} {x x' : PName} :
  --     P.f ∩ Pσ.f = ∅ → P.f \ {x} = {z,..., zₙ} →
  --     ---------------------------------------------------------------------------------
  --     ProcStep (!x.{P}) (x⸨DUP⸩) (z₁⟦DUP⟧⸨z₁σ⸩ ... zₙ⟦DUP⟧⸨zₙσ⸩.x⟦xσ⟧.((!x.P)σ) |ₚ !x.{P})

  | use₁
      {P : Proc} {x : PName} :
      ProcStep (x⟦USE⟧.P) (x⟦USE⟧) P

  | use₂
      {P : Proc} {x : PName} :
      ProcStep (!x.⦃P⦄) (x⸨USE⸩) P

  | output
      {P : Proc} {x : PName} {A : Types} :
      ProcStep (x⟦A⟧:P) (x⟦A⟧:) P

  | input
      {P : Proc} {x : PName} {A : Types} {X : TVar}:
      ProcStep (x⸨X⸩:P) (x⸨A⸩:) (P⦃A // X⦄ₜ)

  | selectL
      {P : Proc} {x : PName} :
      ProcStep (x⟦𝐋⟧.P) (x⟦𝐋⟧) P

  | offerL
      {P Q : Proc} {x : PName} :
      ProcStep (⸨x⸩.case⦃𝐋 : P, 𝐑 : Q⦄) (x⸨𝐋⸩) P

  | selectR
      {P : Proc} {x : PName} :
      ProcStep (x⟦𝐑⟧.P) (x⟦𝐑⟧) P

  | offerR
      {P Q : Proc} {x : PName} :
      ProcStep (⸨x⸩.case⦃𝐋 : P, 𝐑 : Q⦄) (x⸨𝐑⸩) Q

  | link₁
      {x y : PName} :
      ProcStep (x ⟷ₚ y) (x ⟷ₗ y) 𝟘

  | link₂
      {x y : PName} :
      ProcStep (x ⟷ₚ y) (y ⟷ₗ x) 𝟘

  | com {P P' : Proc} {x y : PName} {μ : Mu} :
      ProcStep P (x⟦μ⟧ₘ |ₗ y⟦μ⟧ₘ) P' →
      -------------------------------------
      ProcStep (𝑣⸨x, y⸩ P) (τ) (𝑣⸨x, y⸩ P')

  | axcut
      {P P' : Proc} {x y z : PName} :
      ProcStep P (x ⟷ₗ y) P' →
      --------------------------------------
      ProcStep (𝑣⸨y, z⸩ P) (τ) (P'⦃x // z⦄ₙ)

notation:50 P " -[" l "]->ₚ " P' => ProcStep P l P'

inductive MPST : (P : Proc) → Lbls → (P' : Proc) → Prop where
  | refl
    {P : Proc} :
    ------------
    MPST P (ε) P

  | stepR {l : Lbl} {ls : Lbls} {P P'' P' : Proc} :
    (MPST P ls P'') → (P'' -[l]->ₚ P') →
    ------------------------------------
          MPST P (ls ∷ₗ l) P'

notation:50 P " -[" ls "]->>ₚ " P' => MPST P ls P'

------------------------- ENV-FUCNTION & TRANSITION RULES --------------------------

def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  | one
      {x : PName} :
      EnvStep (x ∶ 1) (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep (Γ‚ Δ‚ x ∶ A ⊗ B) (x⟦x'⟧) (Γ‚ x'∶ A |ₕ Δ‚ x ∶ B)

  | bot
      {Γ : Env} {x : PName} :
      EnvStep (Γ‚ x ∶ ⊥) (x⸨⸩) Γ

  | parr
      {Γ Δ : Env} {x x' : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⅋ B) (x⸨x'⸩) (Γ‚ x' ∶ A‚ Δ‚ x ∶ B)

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
      EnvStep (𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ Γ) →
      ------------------------------------------------------
      EnvStep (𝒢 |ₕ Γ) (τ) (𝒢 |ₕ Γ)

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': PName} {A B : Types} :
      EnvStep
        (𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⊗ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ)
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B |ₕ Ξ‚ y' ∶ Aᗮ‚ y ∶ Bᗮ) →
      ---------------------------------------------------
      EnvStep (𝒢 |ₕ Γ‚ Δ‚ Ξ) (τ) (𝒢 |ₕ Γ‚ Δ‚ Ξ)

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : PName} {A B : Types} {l : Lbl} :
      EnvStep (𝒢 |ₕ Γ‚ x ∶ Aᗮ |ₕ Δ‚ y ∶ A) (l) (𝒢' |ₕ Γ'‚ x ∶ Aᗮ |ₕ Δ'‚ y ∶ A) →
      ----------------------------------------------------------------------------
      EnvStep (𝒢 |ₕ Γ‚ Δ) l (𝒢' |ₕ Γ'‚ Δ')

  | selectL
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧) (Γ‚ x ∶ A)

  | offerL
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A & B) (x⸨𝐋⸩) (Γ‚ x ∶ A)

  | selectR
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧) (Γ‚ x ∶ B)

  | offerR
      {Γ : Env} {x : PName} {A B : Types} :
      EnvStep (Γ‚ x ∶ A & B) (x⸨𝐑⸩) (Γ‚ x ∶ B)

  | link₁
      {x y : PName} {A : Types} :
      EnvStep (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₗ y) ∅

  | link₂ -- FIXME this one isn't actually in the definition in Fig 8, but it matches ProcStep
      {x y : PName} {A : Types} :
      EnvStep (x ∶ Aᗮ‚ y ∶ A) (y ⟷ₗ x) ∅

  | use₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ?ₜA) (x⟦USE⟧) (Γ‚ x ∶ A)

  | use₂
      {Γ : Env} {x : PName} {A : Types} :
      ?ₑΓ →
      --------------------------------------
      EnvStep (Γ‚ x ∶ !ₜA) (x⸨USE⸩) (Γ‚ x ∶ A)

  | disp₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ?ₜA) (x⟦DISP⟧) (Γ‚ x ∶ ⊥)

  | disp₂
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep {Γ‚ x ∶ !ₜA} (x⸨DISP⸩) (Γ‚ x ∶ 1)

  | dup₁
      {Γ : Env} {x : PName} {A : Types} :
      EnvStep (Γ‚ x ∶ ?ₜA) (x⟦DUP⟧) (Γ‚ x ∶ ?ₜA ⅋ ?ₜA)

  | dup₂
      {Γ : Env} {x : PName} {A : Types} :
      ?ₑΓ →
      ----------------------------------------------
      EnvStep (Γ‚ x ∶ !ₜA) (x⸨DUP⸩) (Γ‚ x ∶ !ₜA ⊗ !ₜA)

  | output
      {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
      EnvStep (Γ‚ x ∶ ∃⸨X⸩.B) (x⟦A⟧:) (Γ‚ x ∶ B{A // X})

  | input
      {Γ : Env} {x : PName} {A B : Types} {X : TVar} :
      EnvStep (Γ‚ x ∶ ∀⸨X⸩.B) (x⸨A⸩:) (Γ‚ x ∶ B{A // X})

notation:50 P " -[" l "]->ₑ " P' => EnvStep P l P'

inductive MEST : (𝒢 : HyperEnv) → Lbls → (𝒢' : HyperEnv) → Prop where
  | refl
    {𝒢 : HyperEnv} :
    -------------
    MEST 𝒢 (ε) 𝒢

  | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢'' 𝒢' : HyperEnv} :
    (MEST 𝒢 ls 𝒢'') → (𝒢'' -[l]->ₑ 𝒢') →
    ------------------------------------
          MEST 𝒢 (ls ∷ₗ l) 𝒢'

notation:50 𝒢 " -[" ls "]->>ₑ " 𝒢' => MPST 𝒢 ls 𝒢'
