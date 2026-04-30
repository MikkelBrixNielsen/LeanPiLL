import PiLL.Model.STypes.Basic

def TVar.lc : Nat → TVar → Prop
  | _, .free _ => True
  | k, .bound i => i < k

def Types.lc : Nat → Types → Prop
  | _, .atom _      => True
  | _, .atomDual _  => True
  | k, .var v       => TVar.lc k v
  | k, .varDual v   => TVar.lc k v
  | _, .one         => true
  | _, .bot         => true
  | k, .tensor A B  => A.lc k ∧ B.lc k
  | k, .parr A B    => A.lc k ∧ B.lc k
  | k, .oplus A B   => A.lc k ∧ B.lc k
  | k, .amp A B     => A.lc k ∧ B.lc k
  | k, .bang A => A.lc k
  | k, .quest A => A.lc k
  | k, .forall_ A => A.lc (k+1)
  | k, .exists_ A => A.lc (k+1)

def Types.lc_0 : Types → Prop := Types.lc 0

def Types.pos : Types → Prop
  | .atom _ => True
  | .var _ => True
  | .one => True
  | .tensor _ _ => True
  | .oplus _ _ => True
  | .bang _ => True
  | .exists_ _ => True
  | _ => False

def Types.neg : Types → Prop
  | .atomDual _ => True
  | .varDual _ => True
  | .bot => True
  | .parr _ _ => True
  | .amp _ _ => True
  | .quest _ => True
  | .forall_ _ => True
  | _ => False

instance Types.positive_decidable (A : Types) : Decidable A.pos := by
  unfold Types.pos
  split <;> infer_instance

instance Types.negative_decidable (A : Types) : Decidable A.neg := by
  unfold Types.neg
  split <;> infer_instance

def Types.freeTypes : Types → Finset TVar
  | .atom _ | .atomDual _ | .one | .bot => ∅
  | .var v        => {v}
  | .varDual v    => {v}
  | .tensor A B   => A.freeTypes ∪ B.freeTypes
  | .parr A B     => A.freeTypes ∪ B.freeTypes
  | .oplus A B    => A.freeTypes ∪ B.freeTypes
  | .amp A B      => A.freeTypes ∪ B.freeTypes
  | .bang A       => A.freeTypes
  | .quest A      => A.freeTypes
  | .forall_ A  => A.freeTypes
  | .exists_ A   => A.freeTypes

attribute [simp] Types.freeTypes
def Types.isServerUsable : Types → Prop
  | .quest _  => True
  | _         => False
