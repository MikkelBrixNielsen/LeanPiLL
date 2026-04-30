import PiLL.Model.Processes.Basic
import PiLL.Model.STypes.Properties

def Channel.lc : Nat → Channel → Prop
  | _, .free _    => True
  | k, .bound i   => i < k

def Finset.lc (zs : Finset Channel) (k : Nat) : Prop :=
  ∀ z ∈ zs, z.lc k

def Proc.lc : Nat → Nat → Proc → Prop
  | _, _, .nil              => True
  | k, n, .one x P          => x.lc k ∧ P.lc k n
  | k, n, .bot x P          => x.lc k ∧ P.lc k n
  | k, n, .tensor x P       => x.lc k ∧ P.lc (k + 1) n
  | k, n, .parr x P         => x.lc k ∧ P.lc (k + 1) n
  | k, n, .cut P            => P.lc (k + 2) n
  | k, n, .par P Q          => P.lc k n ∧ Q.lc k n
  | k, n, .selectL x P      => x.lc k ∧ P.lc k n
  | k, n, .selectR x P      => x.lc k ∧ P.lc k n
  | k, n, .amp x P Q        => x.lc k ∧ P.lc k n ∧ Q.lc k n
  | k, n, .output x P A     => x.lc k ∧ P.lc k n ∧ A.lc n
  | k, n, .input x P        => x.lc k ∧ P.lc k (n + 1)
  | k, n, .server x zs P    => x.lc k ∧ zs.lc k ∧ P.lc k n
  | k, n, .consume x P      => x.lc k ∧ P.lc k n
  | k, n, .duplicate x P    => x.lc k ∧ P.lc (k + 1) n
  | k, n, .dispose x P      => x.lc k ∧ P.lc k n
  | k, _, .link x y         => x.lc k ∧ y.lc k

def Proc.lc_0 : Proc → Prop := Proc.lc 0 0
