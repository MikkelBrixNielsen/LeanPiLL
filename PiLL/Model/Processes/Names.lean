import PiLL.Model.Processes.Basic

def Channel.f : Channel → Finset FPName
  | .free x     => {x}
  | .bound _    => {}

def Finset.f (zs : Finset Channel) : Finset FPName :=
  zs.biUnion Channel.f

def Proc.f : Proc → Finset FPName
  | .tensor x P         => x.f ∪ P.f
  | .parr x P           => x.f ∪ P.f
  | .one x P            => x.f ∪ P.f
  | .bot x P            => x.f ∪ P.f
  | .cut P              => P.f
  | .par P Q            => P.f ∪ Q.f
  | .nil                => {}
  | .selectL x P        => x.f ∪ P.f
  | .selectR x P        => x.f ∪ P.f
  | .amp x P Q          => x.f ∪ P.f ∪ Q.f
  | .output x P _       => x.f ∪ P.f
  | .input  x P         => x.f ∪ P.f
  | .server x zs P      => x.f ∪ zs.f ∪ P.f
  | .consume x P        => x.f ∪ P.f
  | .duplicate x P      => x.f ∪ P.f
  | .dispose x P        => x.f ∪ P.f
  | .link x y           => x.f ∪ y.f
