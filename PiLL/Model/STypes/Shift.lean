import PiLL.Model.STypes.Basic
import PiLL.Model.STypes.Properties

-- d used as cutoff depth, variables < d are locally bound
-- c is correction / shift amount
def TVar.shift (d c : Nat) : TVar → TVar
  | .bound i => if i < d then .bound i else .bound (i + c)
  | .free n => .free n

instance : HasShift TVar where shift v d c := TVar.shift d c v

def Types.shift (d c : Nat) : Types → Types
  | .var v        => .var (v.shift d c)
  | .varDual v    => .varDual (v.shift d c)
  | .forall_ A    => .forall_ (A.shift (d + 1) c)          -- binds 1
  | .exists_ A    => .exists_ (A.shift (d + 1) c)          -- binds 1
  | .tensor A B   => .tensor (A.shift d c) (B.shift d c)
  | .parr A B     => .parr (A.shift d c) (B.shift d c)
  | .quest A      => .quest (A.shift d c)
  | .bang A       => .bang (A.shift d c)
  | .amp A B      => .amp (A.shift d c) (B.shift d c)
  | .oplus A B    => .oplus (A.shift d c) (B.shift d c)
  | t             => t -- one | bot | atom | atomDual (Don't have Types to shift)

instance : HasShift Types where shift T d c := Types.shift d c T
