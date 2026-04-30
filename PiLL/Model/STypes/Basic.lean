import PiLL.Model.Base

abbrev Atom := Nat
abbrev FTVar := Nat
abbrev BTVar := Nat

inductive TVar : Type
  | free    (x : FTVar)
  | bound   (x : BTVar)
deriving DecidableEq, Repr

inductive Types : Type where
  | atom        (a : Atom)
  | atomDual    (a : Atom)
  | var         (v : TVar)
  | varDual     (v : TVar)
  | one
  | bot
  | tensor      (A B : Types)
  | parr        (A B : Types)
  | oplus       (A B : Types)
  | amp         (A B : Types)
  | bang        (A : Types)
  | quest       (A : Types)
  | forall_     (A : Types)           -- Binds 1 Type Variable
  | exists_     (A : Types)           -- Binds 1 Type Variable
deriving DecidableEq, BEq, Repr

def Types.dual : Types → Types
  | .atom a       => .atomDual a
  | .atomDual a   => .atom a
  | .var v        => .varDual v
  | .varDual v    => .var v
  | .one          => .bot
  | .bot          => .one
  | .tensor A B   => .parr (dual A) (dual B)
  | .parr A B     => .tensor (dual A) (dual B)
  | .oplus A B    => .amp (dual A) (dual B)
  | .amp A B      => .oplus (dual A) (dual B)
  | .bang A       => .quest (dual A)
  | .quest A      => .bang (dual A)
  | .forall_ A  => .exists_ (dual A)
  | .exists_ A   => .forall_ (dual A)

def Types.linImpl (A B : Types) : Types := (A.dual).parr B
