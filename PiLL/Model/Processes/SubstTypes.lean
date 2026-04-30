import PiLL.Model.Processes.Basic
import PiLL.Model.STypes.Subst

def Proc.substTypes (A : Types) (k : Nat) : Proc → Proc
  | .nil              => .nil
  | .one x P          => .one x (P.substTypes A k)
  | .bot x P          => .bot x (P.substTypes A k)
  | .tensor x P       => .tensor x (P.substTypes A k)
  | .parr x P         => .parr x (P.substTypes A k)
  | .cut P            => .cut (P.substTypes A k)
  | .par P Q          => .par (P.substTypes A k) (Q.substTypes A k)
  | .selectL x P      => .selectL x (P.substTypes A k)
  | .selectR x P      => .selectR x (P.substTypes A k)
  | .amp x P Q        => .amp x (P.substTypes A k) (Q.substTypes A k)
  | .output x P B     => .output x (P.substTypes A k) (B.subst A k)
  | .input x P        => .input x (P.substTypes (A.shift 0 1) (k + 1))
  | .server x zs P       => .server x zs (P.substTypes A k)
  | .consume x P      => .consume x (P.substTypes A k)
  | .duplicate x P    => .duplicate x (P.substTypes A k)
  | .dispose x P      => .dispose x (P.substTypes A k)
  | .link x y         => .link x y

instance : HasSubst Proc Types Nat where subst P A k := Proc.substTypes A k P

def Proc.shiftTypes (d c : Nat) : Proc → Proc
  | .nil              => .nil
  | .one x P          => .one x (P.shiftTypes d c)
  | .bot x P          => .bot x (P.shiftTypes d c)
  | .tensor x P       => .tensor x (P.shiftTypes d c)
  | .parr x P         => .parr x (P.shiftTypes d c)
  | .cut P            => .cut (P.shiftTypes d c)
  | .par P Q          => .par (P.shiftTypes d c) (Q.shiftTypes d c)
  | .selectL x P      => .selectL x (P.shiftTypes d c)
  | .selectR x P      => .selectR x (P.shiftTypes d c)
  | .amp x P Q        => .amp x (P.shiftTypes d c) (Q.shiftTypes d c)
  | .output x P A     => .output x (P.shiftTypes d c) (A.shift d c)
  | .input x P        => .input x (P.shiftTypes (d + 1) c)
  | .server x zs P    => .server x zs (P.shiftTypes d c)
  | .consume x P      => .consume x (P.shiftTypes d c)
  | .duplicate x P    => .duplicate x (P.shiftTypes d c)
  | .dispose x P      => .dispose x (P.shiftTypes d c)
  | .link x y         => .link x y

instance : HasShiftTypes Proc where shift P d c := Proc.shiftTypes d c P
