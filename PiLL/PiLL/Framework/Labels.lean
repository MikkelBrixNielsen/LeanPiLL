import PiLL.Framework.Process

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

notation "𝐋"    => Mu.L
notation "𝐑"    => Mu.R
notation "USE"  => Mu.USE
notation "DUP"  => Mu.DUP
notation "DISP" => Mu.DISP

notation:80 x"⟦⟧" => HasBracket.brack x ()
notation:80 x"⟦"y"⟧" => HasBracket.brack x y

@[simp] instance : HasBracket PName Unit Act where brack x _ := Act.one x
@[simp] instance : HasBracket PName PName Act where brack x y := Act.tensor x y
@[simp] instance : HasBracket PName Types Act where brack x A := Act.output x A
@[simp] instance : HasBracket PName Mu Act where brack x μ := Act.muBrack x μ

notation:80 x"⸨⸩" => HasParen.paren x ()
notation:80 x"⸨"y"⸩" => HasParen.paren x y

@[simp] instance : HasParen PName Unit Act where paren x _ := Act.bot x
@[simp] instance : HasParen PName PName Act where paren x y := Act.parr x y
@[simp] instance : HasParen PName Types Act where paren x A := Act.input x A
@[simp] instance : HasParen PName Mu Act where paren x μ := Act.muParen x μ

-- Tells Lean to use (HasBracket / HasParen) Act when asked for the Lbl variant
@[simp] instance {S C : Type} [HasBracket S C Act] : HasBracket S C Lbl where
  brack s c := Lbl.act (HasBracket.brack s c)

@[simp] instance {S C : Type} [HasParen S C Act] : HasParen S C Lbl where
  paren s c := Lbl.act (HasParen.paren s c)

notation:80 x "⟷ₗ" y => Lbl.link x y
notation:70 l " |ₗ " l' => Lbl.par l l'
notation:80 "τ" => Lbl.tau

@[app_unexpander Lbl.act]
def unexpandLblAct : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => pure a
  | _ => throw ()
