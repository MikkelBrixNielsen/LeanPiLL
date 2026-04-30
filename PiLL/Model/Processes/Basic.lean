import PiLL.Model.STypes.Basic

abbrev FPName := Nat
abbrev BPName := Nat

inductive Channel : Type where
  | free    (x : FPName)
  | bound   (x : BPName)
deriving DecidableEq, BEq, Repr

prefix:max "#" => Channel.free
prefix:max "$" => Channel.bound

-- parr / tensor / duplicate binds 1 name
-- cut binds 2 names
-- input binds 1 TVar
inductive Proc : Type where
  | nil
  | one         (x : Channel) (P : Proc)
  | bot         (x : Channel) (P : Proc)
  | tensor      (x : Channel) (P : Proc)
  | parr        (x : Channel) (P : Proc)
  | cut         (P : Proc)
  | par         (P Q : Proc)
  | selectL     (x : Channel) (P : Proc)
  | selectR     (x : Channel) (P : Proc)
  | amp         (x : Channel) (P Q : Proc)
  | output      (x : Channel) (P : Proc) (A : Types)
  | input       (x : Channel) (P : Proc)
  | server      (x : Channel) (zs : Finset Channel) (P : Proc)
  | consume     (x : Channel) (P : Proc)
  | duplicate   (x : Channel) (P : Proc)
  | dispose     (x : Channel) (P : Proc)
  | link        (x y : Channel)
deriving DecidableEq, BEq
