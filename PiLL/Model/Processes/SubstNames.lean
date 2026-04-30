import PiLL.Model.Processes.Basic
import PiLL.Model.STypes.Subst

-- R : Replacement, T : Target
def FPName.subst (R T : FPName) : FPName → FPName :=
  (fun x => if x = T then R else x)

instance : HasSubst FPName FPName FPName where subst x R T := FPName.subst R T x

def Channel.subst (R T : FPName) : Channel → Channel
  | .free x => if x == T then .free R else .free x
  | .bound i => .bound i

instance : HasSubst Channel FPName FPName where subst C R T := Channel.subst R T C

def Finset.subst (zs : Finset Channel) (R T : FPName) : Finset Channel :=
  zs.image (fun u => u.subst R T)

instance : HasSubst (Finset Channel) FPName FPName where subst S R T := Finset.subst S R T

def Proc.substNames (R T : FPName) : Proc → Proc
  | .nil              => .nil
  | .one x P          => .one (x.subst R T) (P.substNames R T)
  | .bot x P          => .bot (x.subst R T) (P.substNames R T)
  | .tensor x P       => .tensor (x.subst R T) (P.substNames R T)
  | .parr x P         => .parr (x.subst R T) (P.substNames R T)
  | .cut P            => .cut (P.substNames R T)
  | .par P Q          => .par (P.substNames R T) (Q.substNames R T)
  | .selectL x P      => .selectL (x.subst R T) (P.substNames R T)
  | .selectR x P      => .selectR (x.subst R T) (P.substNames R T)
  | .amp x P Q        => .amp (x.subst R T) (P.substNames R T) (Q.substNames R T)
  | .output x P A     => .output (x.subst R T) (P.substNames R T) A
  | .input x P        => .input (x.subst R T) (P.substNames R T)
  | .server x zs P       => .server (x.subst R T) (zs.subst R T) (P.substNames R T)
  | .consume x P      => .consume (x.subst R T) (P.substNames R T)
  | .duplicate x P    => .duplicate (x.subst R T) (P.substNames R T)
  | .dispose x P      => .dispose (x.subst R T) (P.substNames R T)
  | .link x y         => .link (x.subst R T) (y.subst R T)

instance : HasSubst Proc FPName FPName where subst P R T := Proc.substNames R T P

-- FIXME: Relic from the past before LN
--        Remove HasShiftNames and such
-- def Proc.shiftNames (d c : Nat) : Proc → Proc
--   | .nil              => .nil
--   | .one x P          => .one x (P.shiftNames d c)
--   | .bot x P          => .bot x (P.shiftNames d c)
--   | .tensor x P       => .tensor x (P.shiftNames (d + 1) c)
--   | .parr x P         => .parr x (P.shiftNames (d + 1) c)
--   | .cut P            => .cut (P.shiftNames (d + 2) c)
--   | .par P Q          => .par (P.shiftNames d c) (Q.shiftNames d c)
--   | .selectL x P      => .selectL x (P.shiftNames d c)
--   | .selectR x P      => .selectR x (P.shiftNames d c)
--   | .amp x P Q        => .amp x (P.shiftNames d c) (Q.shiftNames d c)
--   | .output x P A     => .output x (P.shiftNames d c) A
--   | .input x P        => .input x (P.shiftNames d c)
--   | .server x zs P    => .server x zs (P.shiftNames d c)
--   | .consume x P      => .consume x (P.shiftNames d c)
--   | .duplicate x P    => .duplicate x (P.shiftNames (d + 1) c)
--   | .dispose x P      => .dispose x (P.shiftNames d c)
--   | .link x y         => .link x y

-- instance : HasShiftNames Proc where shift P d c := Proc.shiftNames d c P
