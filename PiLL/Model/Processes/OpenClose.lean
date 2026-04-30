import PiLL.Model.Processes.Basic

def Channel.open (u v : Channel) (k : Nat) : Channel :=
  match u with
  | Channel.bound i => if i == k then v else Channel.bound i
  | c => c

instance : HasOpen Channel Channel Nat where open_ u v k := Channel.open u v k

def Finset.open (zs : Finset Channel) (v : Channel) (k : Nat) : Finset Channel :=
  zs.image (fun u => u.open v k)

instance : HasOpen (Finset Channel) Channel Nat where open_ zs v k := Finset.open zs v k

def Proc.open (P : Proc) (u : Channel) (k : Nat) : Proc :=
  match P with
  | .nil              => .nil
  | .one x P          => .one (x.open u k) (P.open u k)
  | .bot x P          => .bot (x.open u k) (P.open u k)
  | .tensor x P       => .tensor (x.open u k) (P.open u (k + 1))
  | .parr x P         => .parr (x.open u k) (P.open u (k + 1))
  | .cut P            => .cut (P.open u (k + 2))
  | .par P Q          => .par (P.open u k) (Q.open u k)
  | .server x zs P    => .server (x.open u k) (zs.open u k) (P.open u k)
  | .duplicate x P    => .duplicate (x.open u k) (P.open u (k + 1))
  | .consume x P      => .consume (x.open u k) (P.open u k)
  | .dispose x P      => .dispose (x.open u k) (P.open u k)
  | .selectL x P      => .selectL (x.open u k) (P.open u k)
  | .selectR x P      => .selectR (x.open u k) (P.open u k)
  | .amp x P Q        => .amp (x.open u k) (P.open u k) (Q.open u k)
  | .output x P A     => .output (x.open u k) (P.open u k) A
  | .input x P        => .input (x.open u k) (P.open u k)
  | .link x y         => .link (x.open u k) (y.open u k)

instance : HasOpen Proc Channel Nat where open_ P v k := Proc.open P v k

instance : HasOpenTwo Proc Channel Channel Nat where open_ P u v k :=
  (Proc.open (Proc.open P v (k + 1)) u k)
def Channel.close (u : Channel) (x : FPName) (k : Nat) : Channel :=
  match u with
  | Channel.free name => if x == name then .bound k else .free name
  | .bound i  => .bound i

instance : HasClose Channel FPName Nat where close_ u x k := Channel.close u x k

def Finset.close (zs : Finset Channel) (x : FPName) (k : Nat) : Finset Channel :=
  zs.image (fun u => u.close x k)

instance : HasClose (Finset Channel) FPName Nat where close_ zs x k := Finset.close zs x k

-- parr / tensor / duplicate binds 1
-- cut binds 2
def Proc.close (P : Proc) (z : FPName) (k : Nat) : Proc :=
  match P with
  | .nil => .nil
  | .one x P          => .one (x.close z k) (P.close z k)
  | .bot x P          => .bot (x.close z k) (P.close z k)
  | .tensor x P       => .tensor (x.close z k) (P.close z (k + 1))
  | .parr x P         => .parr (x.close z k) (P.close z (k + 1))
  | .cut P            => .cut (P.close z (k + 2))
  | .par P Q          => .par (P.close z k) (Q.close z k)
  | .selectL x P      => .selectL (x.close z k) (P.close z k)
  | .selectR x P      => .selectR (x.close z k) (P.close z k)
  | .amp x P Q        => .amp (x.close z k) (P.close z k) (Q.close z k)
  | .output x P A     => .output (x.close z k) (P.close z k) A
  | .input x P        => .input (x.close z k) (P.close z k)
  | .server x zs P    => .server (x.close z k) (zs.close z k) (P.close z k)
  | .consume x P      => .consume (x.close z k) (P.close z k)
  | .duplicate x P    => .duplicate (x.close z k) (P.close z (k + 1))
  | .dispose x P      => .dispose (x.close z k) (P.close z k)
  | .link x y         => .link (x.close z k) (y.close z k)

instance : HasClose Proc FPName Nat where close_ P x k := Proc.close P x k

instance : HasCloseTwo Proc FPName FPName Nat where close_ P x y k :=
  (Proc.close (Proc.close P y (k + 1)) x k)
