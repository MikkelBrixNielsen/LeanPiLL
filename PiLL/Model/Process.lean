import PiLL.Model.STypes

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

notation:80 x "⟦⟧․" P => Proc.one x P
notation:80 x "⟦$N⟧․" P => Proc.tensor x P
notation:80 x "⟦" A "⟧․" P => Proc.output x P A
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 x "⸨$N⸩․" P => Proc.parr x P
notation:80 x "⸨$T⸩․" P => Proc.input x P

notation:75 "𝑣⸨$N,$N⸩ " P:80 => Proc.cut P
notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
notation:80 x "⟦DUP⟧⸨$N⸩․" P:80 => Proc.duplicate x P
notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
notation:80 "!" x "․{" P:80 "}" => Proc.server x ∅ P
notation:80 "!" x "⟨" zs "⟩․{" P:80 "}" => Proc.server x zs P
notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

notation:80 x "⟷ₚ" y => Proc.link x y
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil

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

def freshName (s : Finset FPName) : FPName :=
  s.sup id + 1

lemma fresh_is_fresh (s : Finset FPName) (x : FPName) (h : x ∈ s) :
  id x < freshName s := by
  have hxle : x ≤ s.sup id := by
    have : id x ≤ s.sup id := Finset.le_sup h
    exact this
  exact Nat.lt_succ_of_le hxle

lemma exists_one_fresh (L : Finset FPName) :
  ∃u, u ∉ L := by
  let u := freshName L
  use u
  intro hc
  have h_lt := fresh_is_fresh L u hc
  exact Nat.lt_irrefl _ h_lt

lemma exists_two_fresh (L : Finset FPName) :
  ∃ u v, u ∉ L ∧ v ∉ L ∧ u ≠ v := by
  let u := freshName L
  have hu : u ∉ L := by
    intro hc
    have h_lt := fresh_is_fresh L u hc
    exact Nat.lt_irrefl _ h_lt
  let v := freshName (L ∪ {u})
  have hv : v ∉ L := by
    intro hc
    have hin : v ∈ L ∪ {u} := Finset.mem_union_left {u} hc
    have h_lt := fresh_is_fresh (L ∪ {u}) v hin
    exact Nat.lt_irrefl _ h_lt
  have hneq : u ≠ v := by
    intro heq
    have hinu : v ∈ ({u} : Finset FPName) := by rw [← heq] ; simp
    have hinLu : v ∈ L ∪ {u} := by rw [← heq] ; simp
    have h_lt := fresh_is_fresh (L ∪ {u}) v hinLu
    exact Nat.lt_irrefl _ h_lt
  refine ⟨u, v, hu, hv, hneq⟩

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

@[simp] lemma FPName.subst_id {x z : FPName} :
  z{x // x} = z := by
  simp only [HasSubst.subst, FPName.subst, ite_eq_right_iff]
  intro h
  apply h.symm

@[simp] lemma FPName.subst_self {x y : FPName} :
  x{y // x} = y := by simp [HasSubst.subst, FPName.subst]

@[simp] lemma FPName.subst_self_of_ne {x y z : FPName} (hneq : z ≠ x) :
  z{y // x} = z := by
  simp only [HasSubst.subst, FPName.subst, ite_eq_right_iff]
  intro h
  contradiction

lemma FPName.subst_preserves_neq {w x y z : FPName}
  (hab : w ≠ z) (hya : y = w → y = x) (hyb : y = z → y = x) :
  w{y // x} ≠ z{y // x} := by
  simp only [HasSubst.subst, FPName.subst]
  split_ifs <;> simp_all only [ne_eq, not_true_eq_false,
    not_false_eq_true, implies_true, imp_false]
  all_goals {
    intro heq
    exact hya heq.symm
  }

@[simp] lemma Channel.subst_free {x y z : FPName} :
  (#z){y // x} = #(z{y // x}) := by
  simp [HasSubst.subst, Channel.subst, FPName.subst]
  split_ifs <;> simp

@[simp] lemma Channel.subst_bound {x y : FPName} {i : Nat} :
  (Channel.bound i){y // x} = Channel.bound i := by
  simp [HasSubst.subst, Channel.subst]

@[simp] lemma Channel.subst_self {u : Channel} {x : FPName} :
  u.subst x x = u := by
  cases u <;> simp_all [Channel.subst]

@[simp] lemma Channel.subst_self_notation {u : Channel} {x : FPName} :
  u{x // x} = u := by
  induction u generalizing x <;> simp_all [HasSubst.subst, Channel.subst]

@[simp] lemma Finset.subst_self {zs : Finset Channel} {x : FPName} :
  zs.subst x x = zs := by
  simp [Finset.subst]

@[simp] lemma Proc.substNames_self {P : Proc} {x : FPName} :
  P{x // x} = P := by
  induction P generalizing x <;> simp_all [HasSubst.subst, Proc.substNames]

@[simp] lemma Proc.substNames_par {P Q : Proc} {x y : FPName} :
  (P |ₚ Q){y // x} = P{y // x} |ₚ (Q{y // x}) := by
  simp [HasSubst.subst, Proc.substNames]

macro "simp_Proc_substNames" : tactic =>
  `(tactic|
    (simp [HasSubst.subst, Proc.substNames, Finset.subst, Channel.subst, FPName.subst] ;
      try (split_ifs <;> try constructor <;> rfl)))

@[simp] lemma Proc.substNames_nil {x y : FPName} :
  𝟘{y // x} = 𝟘 := by simp_Proc_substNames

@[simp] lemma Proc.substNames_one {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦⟧․P){y // x} = (u{y // x}⟦⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_bot {P : Proc} {u : Channel} {x y : FPName} :
  (u⸨⸩․P){y // x} = (u{y // x}⸨⸩․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_cut {P : Proc} {x y : FPName} :
  (𝑣⸨$N,$N⸩P){y // x} = 𝑣⸨$N,$N⸩P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_tensor {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦$N⟧․P){y // x} = u{y // x}⟦$N⟧․P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_parr {P : Proc} {u : Channel} {x y : FPName} :
  (u⸨$N⸩․P){y // x} = u{y // x}⸨$N⸩․P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_oplus₁ {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦𝐋⟧․P){y // x} = (u{y // x}⟦𝐋⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_oplus₂ {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦𝐑⟧․P){y // x} = (u{y // x}⟦𝐑⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_amp {P Q : Proc} {u : Channel} {x y : FPName} :
  u․case{𝐋 : P, 𝐑 : Q}{y // x} = u{y // x}․case{𝐋 : P{y // x}, 𝐑 : Q{y // x}} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_quest {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦USE⟧․P){y // x} = (u{y // x}⟦USE⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_bang_empty {P : Proc} {u : Channel} {x y : FPName} :
  !u․{P}{y // x} = !u{y // x}․{P{y // x}} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_bang {P : Proc} {zs : Finset Channel} {u : Channel} {x y : FPName} :
  !u⟨zs⟩․{P}{y // x} = !u{y // x}⟨zs{y // x}⟩․{P{y // x}} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_w {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦DISP⟧․P){y // x} = (u{y // x}⟦DISP⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_c {P : Proc} {u : Channel} {x y : FPName} :
  (u⟦DUP⟧⸨$N⸩․P){y // x} = (u{y // x}⟦DUP⟧⸨$N⸩․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_exists {P : Proc} {u : Channel} {x y : FPName} {A : Types} :
  (u⟦A⟧․P){y // x} = (u{y // x}⟦A⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_forall {P : Proc} {u : Channel} {x y : FPName} :
  (u⸨$T⸩․P){y // x} = (u{y // x}⸨$T⸩․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_ax {u v : Channel} {x y : FPName} :
  (u⟷ₚv){y // x} = (u{y // x}⟷ₚv{y // x}) := by
  simp_Proc_substNames

lemma Proc.shiftTypes_open_comm {n d c : Nat} {P : Proc} {u : Channel} :
  (P.open u n) ↑ᵗ d, c = (P ↑ᵗ d, c).open u n := by
  induction P generalizing d n <;> simp_all [Proc.open, HasShiftTypes.shift, Proc.shiftTypes]

lemma Proc.shiftTypes0_open0_comm {c : Nat} {P : Proc} {u : Channel} :
  (P⸨u⸩) ↑ᵗ c = (P ↑ᵗ c)⸨u⸩ := Proc.shiftTypes_open_comm

lemma Proc.shiftTypes_open0_comm {d c : Nat} {P : Proc} {u : Channel} :
  (P⸨u⸩) ↑ᵗ d, c = (P ↑ᵗ d, c)⸨u⸩ := Proc.shiftTypes_open_comm

lemma Proc.shiftTypes_openCut_comm {P : Proc} {x y : Channel} {d c : Nat} :
  (P⸨x, y⸩) ↑ᵗ d, c = (P ↑ᵗ d, c)⸨x, y⸩ := by
  simp [HasOpenTwo.open_, Proc.shiftTypes_open_comm]

@[simp] lemma Proc.substTypes_ax {u v : Channel} {A : Types} {k : Nat} :
  (u ⟷ₚ v){A // k} = (u ⟷ₚ v) := by simp [HasSubst.subst, Proc.substTypes]

@[simp] lemma Proc.substTypes_par {P Q : Proc} {A : Types} {k : Nat} :
  (P |ₚ Q){A // k} = P{A // k} |ₚ Q{A // k} := by simp [HasSubst.subst, Proc.substTypes]

@[simp] lemma Proc.open_substTypes_comm {P : Proc} {u : Channel} {A : Types} {d i : Nat} :
  (P.open u d).substTypes A i = (P.substTypes A i).open u d := by
  induction P generalizing A i d u <;> simp_all [Proc.open, Channel.open, Proc.substTypes]

@[simp] lemma Proc.open_substTypes_comm_notation {P : Proc} {u : Channel} {A : Types} {i : Nat} :
  P⸨u⸩{A // i} = P{A // i}⸨u⸩ := Proc.open_substTypes_comm

@[simp] lemma Proc.openCut_substTypes_comm {P : Proc} {u v : Channel} {A : Types} {i : Nat} :
  (P⸨u, v⸩).substTypes A i = (P.substTypes A i)⸨u, v⸩:= by
  induction P generalizing A i u <;>
    simp_all [HasOpenTwo.open_, Proc.open, Channel.open, Proc.substTypes]

@[simp] lemma Proc.openCut_substTypes_comm_notation
  {P : Proc} {u v : Channel} {A : Types} {i : Nat} :
  (P⸨u, v⸩){A // i} = (P{A // i})⸨u, v⸩ := Proc.openCut_substTypes_comm

@[simp] lemma Channel.open_substNames_intro_gen (x : Channel) (k : Nat) {w z : FPName}
  (hF : w ∉ x.f) :
  x.open (#z) k = (x.open (#w) k).subst z w := by
  cases x with
  | bound i =>
    simp [Channel.open, Channel.subst]
    split_ifs <;> simp only [↓reduceIte]
  | free f =>
    simp only [Channel.f, Finset.mem_singleton, Channel.open,
      subst, beq_iff_eq, right_eq_ite_iff, free.injEq] at ⊢ hF
    intro h
    exfalso
    exact hF h.symm

@[simp] lemma Finset.open_substNames_intro_gen (zs : Finset Channel) (k : Nat) {w z : FPName}
  (hF : w ∉ zs.f) :
  zs.open (#z) k = (zs.open (#w) k).subst z w := by
  simp only [Finset.open, Finset.subst, Finset.image_image]
  apply Finset.image_congr
  intro u hu
  have hFu : w ∉ u.f := by
    intro contra
    apply hF
    simp only [Finset.f, Finset.mem_biUnion]
    exact ⟨u, hu, contra⟩
  exact Channel.open_substNames_intro_gen u k hFu

set_option linter.flexible false in -- FIXME: Fix linter warnings
lemma Proc.open_substNames_intro_gen (P : Proc) (k : Nat) {w z : FPName} (hF : w ∉ P.f) :
  P⸨k | #z⸩ = P⸨k | #w⸩{z // w} := by
  induction P generalizing k <;> (
    try simp [Proc.f, HasOpen.open_, HasSubst.subst, Proc.open, Proc.substNames] at ⊢ hF
  )
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih
    | input ih | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.open_substNames_intro_gen _ _ hF.1, ih _ hF.2⟩
  case server ih =>
    split_ands
    · exact Channel.open_substNames_intro_gen _ _ hF.1
    · exact Finset.open_substNames_intro_gen _ _ hF.2.1
    · exact ih _ hF.2.2
  case cut ih => apply ih _ hF
  case par ihP ihQ => exact ⟨ihP k hF.1, ihQ k hF.2⟩
  case amp ihP ihQ => exact ⟨Channel.open_substNames_intro_gen _ _ hF.1, ihP _ hF.2.1, ihQ _ hF.2.2⟩
  case link =>
    exact ⟨Channel.open_substNames_intro_gen _ _ hF.1, Channel.open_substNames_intro_gen _ _ hF.2⟩

lemma Proc.open_substNames_intro {P : Proc} {w z : FPName} (hF : w ∉ P.f) :
  P⸨#z⸩ = P⸨#w⸩{z // w} := by
  exact Proc.open_substNames_intro_gen P 0 hF

lemma Channel.open_substNames_comm_gen {u : Channel} {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  (u⸨k | #z⸩){y // x} = u{y // x}⸨k | #z⸩ := by
  induction u
  case free =>
    simp [HasOpen.open_, Channel.open, HasSubst.subst, Channel.subst]
    split_ifs <;> simp
  case bound =>
    simp only [HasSubst.subst, subst, HasOpen.open_, Channel.open, beq_iff_eq]
    split_ifs
    case pos => simp only [ite_eq_right_iff, free.injEq] ; intro ; contradiction
    case neg => rfl

lemma Finset.open_substNames_comm_gen {zs : Finset Channel} {x y z : FPName}
  {k : Nat} (hneq : z ≠ x) :
  (zs⸨k | #z⸩){y // x} = zs{y // x}⸨k | #z⸩ := by
  simp only [HasOpen.open_, HasSubst.subst, Finset.open, Finset.subst, Finset.image_image]
  apply Finset.image_congr
  intro u _
  exact Channel.open_substNames_comm_gen hneq

@[simp] lemma Proc.open_nil {x : FPName} {k : Nat} :
  𝟘⸨k | #x⸩ = 𝟘 := by simp [HasOpen.open_, Proc.open]

@[simp] lemma Proc.open_one {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_bot {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⸨⸩․P)⸨k | #x⸩ = u⸨k | #x⸩⸨⸩․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_tensor {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦$N⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦$N⟧․P⸨k + 1 | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_parr {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⸨$N⸩․P)⸨k | #x⸩ = u⸨k | #x⸩⸨$N⸩․P⸨k + 1 | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_cut {P : Proc} {x : FPName} {k : Nat} :
  (𝑣⸨$N,$N⸩ P)⸨k | #x⸩ = 𝑣⸨$N,$N⸩ P⸨k + 2 | #x⸩ := by
  simp [HasOpen.open_ , Proc.open]

@[simp] lemma Proc.open_par {P Q : Proc} {x : FPName} {k : Nat} :
  (P |ₚ Q)⸨k | #x⸩ = P⸨k | #x⸩ |ₚ Q⸨k | #x⸩:= by
  simp [HasOpen.open_, Proc.open]

@[simp] lemma Proc.open_selectL {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦𝐋⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦𝐋⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_selectR {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦𝐑⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦𝐑⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_amp {P Q : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u․case{𝐋 : P, 𝐑 : Q})⸨k | #x⸩ = u⸨k | #x⸩․case{𝐋 : P⸨k | #x⸩, 𝐑 : Q⸨k | #x⸩} := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_output {P : Proc} {u : Channel} {x : FPName} {A : Types} {k : Nat} :
  (u⟦A⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦A⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_input {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⸨$T⸩․P)⸨k | #x⸩ = u⸨k | #x⸩⸨$T⸩․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_empty_server {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (!u․{P})⸨k | #x⸩ = !u⸨k | #x⸩․{P⸨k | #x⸩} := by
  simp [HasOpen.open_, Finset.open, Channel.open, Proc.open]

@[simp] lemma Proc.open_server {P : Proc} {zs : Finset Channel} {u : Channel}
  {x : FPName} {k : Nat} :
  (!u⟨zs⟩․{P})⸨k | #x⸩ = !u⸨k | #x⸩⟨zs⸨k | #x⸩⟩․{P⸨k | #x⸩} := by
  simp [HasOpen.open_, Finset.open, Channel.open, Proc.open]

@[simp] lemma Proc.open_consume {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦USE⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦USE⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_duplicate {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦DUP⟧⸨$N⸩․P)⸨k | #x⸩ = u⸨k | #x⸩⟦DUP⟧⸨$N⸩․P⸨k + 1 | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_dispose {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (u⟦DISP⟧․P)⸨k | #x⸩ = u⸨k | #x⸩⟦DISP⟧․P⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

@[simp] lemma Proc.open_link {u v : Channel} {x : FPName} {k : Nat} :
  (u⟷ₚv)⸨k | #x⸩ = u⸨k | #x⸩⟷ₚv⸨k | #x⸩ := by
  simp [HasOpen.open_, Channel.open, Proc.open]

set_option linter.flexible false in -- FIXME: Fix linter warnings
lemma Proc.open_substNames_comm_gen {P : Proc} {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  (P⸨k | #z⸩){y // x} = P{y // x}⸨k | #z⸩ := by
  induction P generalizing k <;> try simp
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.open_substNames_comm_gen hneq, ih⟩
  case server u zs P ih =>
    split_ands
    · exact Channel.open_substNames_comm_gen hneq
    · exact Finset.open_substNames_comm_gen hneq
    · exact ih
  case cut ih => exact ih
  case par ihP ihQ => exact ⟨ihP, ihQ⟩
  case amp ihP ihQ => exact ⟨Channel.open_substNames_comm_gen hneq, ⟨ihP, ihQ⟩⟩
  case link => simp [Channel.open_substNames_comm_gen hneq]

lemma Proc.open_substNames_comm {P : Proc} {x y z : FPName} (hF : z ≠ x) :
  (P⸨#z⸩){y // x} = (P{y // x})⸨#z⸩ := Proc.open_substNames_comm_gen (k := 0) hF

lemma Proc.openCut_substNames_comm {P : Proc} {x y z w : FPName}
  (hFz : z ≠ x) (hFw : w ≠ x) :
  P⸨#z, #w⸩{y // x} = P{y // x}⸨#z, #w⸩ := by
  simp only [HasOpenTwo.open_, HasSubst.subst, zero_add]
  change ((P⸨1 | #w⸩)⸨#z⸩){y // x} = P{y // x}⸨1 | #w⸩⸨#z⸩
  rw [Proc.open_substNames_comm_gen (k := 0) hFz]
  rw [Proc.open_substNames_comm_gen (k := 1) hFw]

@[simp] lemma Channel.open_free_not_eq {x y : FPName} {k : Nat} :
  (#x)⸨k | #y⸩ = (#x) := by simp [HasOpen.open_, Channel.open]

@[simp] lemma Channel.close_open_self {x y : FPName} {k : Nat} :
  ((#x).close x k).open #y k = #y := by
  simp [Channel.close, Channel.open]

@[simp] lemma Channel.close_open_self_notation {x y : FPName} {k : Nat} :
  ((#x)⟪k | x⟫)⸨k | #y⸩ = #y := by
  simp [HasClose.close_, HasOpen.open_]

@[simp] lemma Channel.close_open_other {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  ((#z).close x k).open #y k = #z := by
  simp only [Channel.close, Channel.open, beq_iff_eq]
  split_ifs
  case pos h => subst h ; contradiction
  case neg h => simp

@[simp] lemma Channel.close_open_other_notation {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  ((#z)⟪k | x⟫)⸨k | #y⸩ = #z := by
  simp_all [HasClose.close_, HasOpen.open_]

@[simp] lemma Channel.close_open_bound {i k : Nat} {x y : FPName} (hneq : i ≠ k) :
  ((Channel.bound i).close x k).open #y k = .bound i := by
  simp_all [Channel.close, Channel.open]

@[simp] lemma Channel.close_open_bound_notation {i k : Nat} {x y : FPName} (hneq : i ≠ k) :
  (Channel.bound i)⟪k | x⟫⸨k | #y⸩ = .bound i := by
  simp_all [HasClose.close_, HasOpen.open_]

lemma Channel.close_open_eq_substNames {u : Channel} {x y : FPName} {k : Nat}
  (hy : y ∉ u.f) (hlc : u.lc k) : (Channel.close u x k).open (#y) k = u{y // x} := by
  cases u with
  | bound i =>
    simp only [Channel.close, Channel.open, HasSubst.subst, Channel.subst]
    split_ifs
    case pos h =>
      simp [Channel.lc] at h hlc
      grind
    case neg h => rfl
  | free z =>
    simp only [Channel.f, Finset.mem_singleton] at hy
    simp only [Channel.open, Channel.close, beq_iff_eq, HasSubst.subst, subst]
    split_ifs
    case pos h1 h2 => subst h1 ; simp
    case neg h1 h2 => subst h1 ; contradiction
    case pos h1 h2 => subst h2 ; contradiction
    case neg h1 h2 => simp

lemma Channel.close_open_eq_substNames_notation {u : Channel} {x y : FPName} {k : Nat}
  (hy : y ∉ u.f) (hlc : u.lc k) : u⟪k | x⟫⸨k | (#y)⸩ = u{y // x} := by
  simp only [HasClose.close_, HasOpen.open_]
  rw [Channel.close_open_eq_substNames hy hlc]

lemma Finset.close_open_eq_substNames {zs : Finset Channel} {x y : FPName} {k : Nat}
  (hy : y ∉ zs.f) (hlc : zs.lc k) : (zs.close x k).open (#y) k = zs.subst y x := by
  simp only [Finset.close, Finset.open, Finset.subst, Finset.image_image]
  apply Finset.image_congr
  intro u hu
  have hy_u : y ∉ u.f := by
    intro contra
    apply hy
    simp only [Finset.f, Finset.mem_biUnion]
    exact ⟨u, hu, contra⟩
  have hlc_u : u.lc k := hlc u hu
  exact Channel.close_open_eq_substNames hy_u hlc_u

lemma Finset.close_open_eq_substNames_notation {zs : Finset Channel} {x y : FPName} {k : Nat}
  (hy : y ∉ zs.f) (hlc : zs.lc k) : zs⟪k | x⟫⸨k | #y⸩ = zs{y // x} := by
  simp only [HasClose.close_, HasOpen.open_, HasSubst.subst]
  rw [Finset.close_open_eq_substNames hy hlc]

@[simp] lemma Proc.close_nil {k : Nat} {x : FPName} :
  𝟘⟪k | x⟫ = 𝟘 := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_one {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_bot {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⸨⸩․P)⟪k | x⟫ = u⟪k | x⟫⸨⸩․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_tensor {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦$N⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦$N⟧․P⟪k + 1 | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_parr {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⸨$N⸩․P)⟪k | x⟫ = u⟪k | x⟫⸨$N⸩․P⟪k + 1 | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_cut {k : Nat} {x : FPName} {P : Proc} :
  (𝑣⸨$N,$N⸩ P)⟪k | x⟫ = 𝑣⸨$N,$N⸩ P⟪k + 2 | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_par {k : Nat} {x : FPName} {P Q : Proc} :
  (P |ₚ Q)⟪k | x⟫ = P⟪k | x⟫ |ₚ Q⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_selectL {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦𝐋⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦𝐋⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_selectR {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦𝐑⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦𝐑⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_amp {k : Nat} {x : FPName} {u : Channel} {P Q : Proc} :
  (u․case{𝐋 : P, 𝐑 : Q})⟪k | x⟫ = u⟪k | x⟫․case{𝐋 : P⟪k | x⟫, 𝐑 : Q⟪k | x⟫} := by
  simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_output {k : Nat} {x : FPName} {u : Channel} {P : Proc} {A : Types} :
  (u⟦A⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦A⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_input {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⸨$T⸩․P)⟪k | x⟫ = u⟪k | x⟫⸨$T⸩․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_empty_server {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (!u․{P})⟪k | x⟫ = !u⟪k | x⟫․{P⟪k | x⟫} := by simp [HasClose.close_, Proc.close, Finset.close]

@[simp] lemma Proc.close_server {k : Nat} {x : FPName} {u : Channel}
  {P : Proc} {zs : Finset Channel} :
  (!u⟨zs⟩․{P})⟪k | x⟫ = !u⟪k | x⟫⟨zs⟪k | x⟫⟩․{P⟪k | x⟫} :=
  by simp [HasClose.close_, Proc.close, Finset.close]

@[simp] lemma Proc.close_consume {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦USE⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦USE⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_duplicate {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦DUP⟧⸨$N⸩․P)⟪k | x⟫ = (u⟪k | x⟫⟦DUP⟧⸨$N⸩․P⟪k + 1 | x⟫) := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_dispose {k : Nat} {x : FPName} {u : Channel} {P : Proc} :
  (u⟦DISP⟧․P)⟪k | x⟫ = u⟪k | x⟫⟦DISP⟧․P⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

@[simp] lemma Proc.close_link {k : Nat} {x : FPName} {u v : Channel} :
  (u⟷ₚv)⟪k | x⟫ = u⟪k | x⟫⟷ₚv⟪k | x⟫ := by simp [HasClose.close_, Proc.close]

set_option linter.flexible false in -- FIXME: Fix linter warnings
lemma Proc.close_open_eq_substNames {P : Proc} {x y : FPName} {k n : Nat}
  (hy : y ∉ P.f) (hlc : P.lc k n) :
  P⟪k | x⟫⸨k | #y⸩ = P{y // x} := by
  induction P generalizing k n <;> (
    simp only [Proc.f, Finset.mem_union, not_or, Proc.lc] at hy hlc
    simp
  )
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | input ih
    | consume ih | duplicate ih | dispose ih =>
    constructor
    · exact Channel.close_open_eq_substNames_notation hy.1 hlc.1
    · exact ih hy.2 hlc.2
  case server u zs P ih =>
    split_ands
    · exact Channel.close_open_eq_substNames_notation hy.1.1 hlc.1
    · exact Finset.close_open_eq_substNames_notation hy.1.2 hlc.2.1
    · exact ih hy.2 hlc.2.2
  case cut ih => exact ih hy hlc
  case par ihP ihQ =>
    constructor
    · exact ihP hy.1 hlc.1
    · exact ihQ hy.2 hlc.2
  case amp ihP ihQ  =>
    split_ands
    · exact Channel.close_open_eq_substNames_notation hy.1.1 hlc.1
    · exact ihP hy.1.2 hlc.2.1
    · exact ihQ hy.2 hlc.2.2
  case output ih =>
    constructor
    · exact Channel.close_open_eq_substNames_notation hy.1 hlc.1
    · exact ih hy.2 hlc.2.1
  case link u v =>
    constructor
    · exact Channel.close_open_eq_substNames_notation hy.1 hlc.1
    · exact Channel.close_open_eq_substNames_notation hy.2 hlc.2

lemma Channel.open_lc' {u : Channel} {x : FPName} {k : Nat} (hlc : u.lc k) :
  u.open #x k = u := by
  cases u
  case free => simp [Channel.open]
  case bound =>
    simp [Channel.lc] at hlc
    simp [Channel.open]
    grind

lemma Channel.open_lc {u : Channel} {x : FPName} {k : Nat} (hlc : u.lc k) :
  u⸨k | #x⸩ = u := by
  simp only [HasOpen.open_]
  rw [Channel.open_lc' hlc]

lemma Finset.open_lc {zs : Finset Channel} {x : FPName} {k : Nat} (hlc : zs.lc k) :
  zs⸨k | #x⸩ = zs := by
  simp only [HasOpen.open_, Finset.open]
  ext u
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨u, hin, rfl⟩
    simp only [Channel.open_lc' (hlc u hin), hin]
  · intro hin
    use u, hin
    exact Channel.open_lc' (hlc u hin)

lemma Proc.open_lc {P : Proc} {x : FPName} {k n : Nat} (hlc : P.lc k n) :
  P⸨k | #x⸩ = P := by
  induction P generalizing k n <;> (
    simp only [Proc.lc] at hlc
    simp only [open_nil, open_one, one.injEq, open_bot, bot.injEq, open_tensor, tensor.injEq,
      open_parr, parr.injEq, open_cut, cut.injEq, open_par, par.injEq, open_selectL,
      selectL.injEq, open_selectR, selectR.injEq, open_amp, amp.injEq, open_output,
      output.injEq, and_true, open_input, input.injEq, open_server, server.injEq, open_consume,
       consume.injEq, open_duplicate, duplicate.injEq, open_dispose, dispose.injEq, open_link,
       link.injEq]
  )
  case one ih | bot ih | tensor ih | parr ih |selectL ih | selectR ih | input ih
    | consume ih | duplicate ih | dispose ih =>
    constructor
    · exact Channel.open_lc hlc.1
    · exact ih hlc.2
  case server u zs P ih =>
    split_ands
    · exact Channel.open_lc hlc.1
    · exact Finset.open_lc hlc.2.1
    · exact ih hlc.2.2
  case cut ih => exact ih hlc
  case par ihP ihQ =>
    constructor
    · exact ihP hlc.1
    · exact ihQ hlc.2
  case amp ihP ihQ =>
    split_ands
    · exact Channel.open_lc hlc.1
    · exact ihP hlc.2.1
    · exact ihQ hlc.2.2
  case output ih =>
    constructor
    · exact Channel.open_lc hlc.1
    · apply ih hlc.2.1
  case link =>
    constructor
    · exact Channel.open_lc hlc.1
    · exact Channel.open_lc hlc.2

lemma Proc.open_lc_0 {P : Proc} {x : FPName} {n : Nat} (hlc : P.lc 0 n) :
  P⸨#x⸩ = P := Proc.open_lc (k := 0) hlc

lemma Channel.lc_of_open {u : Channel} {x : FPName} {k : Nat} :
  (u⸨k | #x⸩).lc k → u.lc (k + 1) := by
  cases u with
  | free => simp [Channel.lc]
  | bound =>
    simp only [HasOpen.open_, Channel.open, Channel.lc, beq_iff_eq, Order.lt_add_one_iff]
    split_ifs
    case pos h => simp [h]
    case neg h => grind

lemma Finset.lc_of_open {zs : Finset Channel} {x : FPName} {k : Nat} :
  (zs⸨k | #x⸩).lc k → zs.lc (k + 1) := by
  simp only [HasOpen.open_, Finset.lc]
  intros h z hin
  apply Channel.lc_of_open (x := x)
  apply h
  simp only [HasOpen.open_, Finset.open, Finset.mem_image]
  use z

lemma Proc.lc_of_open_gen {P : Proc} {x : FPName} {k n : Nat} :
  P⸨k | #x⸩.lc k n → P.lc (k + 1) n := by
  induction P generalizing n k <;> (
    try simp only [HasOpen.open_, Proc.open, Proc.lc, and_imp, imp_self]
  )
  case one ih | bot ih | selectL ih | selectR ih | input ih | consume ih | duplicate ih
    | dispose ih =>
    intros hlc1 hlc2
    exact ⟨Channel.lc_of_open hlc1, ih hlc2⟩
  case server ih =>
    intros hlc1 hlc2 hlc3
    exact ⟨Channel.lc_of_open hlc1, Finset.lc_of_open hlc2, ih hlc3⟩
  case tensor ih | parr ih =>
    intros hlc1 hlc2
    exact ⟨Channel.lc_of_open hlc1, ih hlc2⟩
  case cut ih =>
    intros hlc ; exact ih hlc
  case par ihP ihQ =>
    intros hlc1 hlc2
    exact ⟨ihP hlc1, ihQ hlc2⟩
  case amp ihP ihQ =>
    intros hlc1 hlc2 hlc3
    exact ⟨Channel.lc_of_open hlc1, ihP hlc2, ihQ hlc3⟩
  case output ih =>
    intros hlc1 hlc2 hlc3
    exact ⟨Channel.lc_of_open hlc1, ih hlc2, hlc3⟩
  case link =>
    intros hlc1 hlc2
    exact ⟨Channel.lc_of_open hlc1, Channel.lc_of_open hlc2⟩

lemma Proc.lc_of_open_two {P : Proc} {x y : FPName} {k n : Nat} :
  Proc.lc k n P⸨k | #x, #y⸩ → Proc.lc (k + 2) n P := by
  simp only [HasOpenTwo.open_]
  intro h
  exact Proc.lc_of_open_gen (Proc.lc_of_open_gen h)

@[simp] lemma Proc.f_nil :
  𝟘.f = ∅ := by simp [Proc.f]

@[simp] lemma Proc.f_one {P : Proc} {u : Channel} :
  (u⟦⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_bot {P : Proc} {u : Channel} :
  (u⸨⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_tensor {P : Proc} {u : Channel} :
  (u⟦$N⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_parr {P : Proc} {u : Channel} :
  (u⸨$N⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_cut {P : Proc} :
  (𝑣⸨$N,$N⸩ P).f = P.f := by simp [Proc.f]

@[simp] lemma Proc.f_par {P Q : Proc} :
   (P |ₚ Q).f = P.f ∪ Q.f := by simp [Proc.f]

@[simp] lemma Proc.f_selectL {P : Proc} {u : Channel} :
  (u⟦𝐋⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_selectR {P : Proc} {u : Channel} :
  (u⟦𝐑⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_amp {P Q : Proc} {u : Channel} :
  (u․case{𝐋 : P, 𝐑 : Q}).f = u.f ∪ P.f ∪ Q.f := by simp [Proc.f]

@[simp] lemma Proc.f_output {P : Proc} {u : Channel} {A : Types} :
  (u⟦A⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_input {P : Proc} {u : Channel} :
  (u⸨$T⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_empty_server {P : Proc} {u : Channel} :
  (!u․{P}).f = u.f ∪ P.f := by simp [Proc.f, Finset.f]

@[simp] lemma Proc.f_server {P : Proc} {zs : Finset Channel} {u : Channel} :
  (!u⟨zs⟩․{P}).f = u.f ∪ zs.f ∪ P.f := by simp [Proc.f, Finset.f]

@[simp] lemma Proc.f_consume {P : Proc} {u : Channel} :
  (u⟦USE⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_duplicate {P : Proc} {u : Channel} :
  (u⟦DUP⟧⸨$N⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_dispose {P : Proc} {u : Channel} :
  (u⟦DISP⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_link {u v : Channel} :
  (u⟷ₚv).f = u.f ∪ v.f := by simp [Proc.f]

@[simp] lemma Channel.f_open_erase {k : Nat} {u : Channel} {y : FPName} (hy : y ∉ u.f) :
  (u⸨k | #y⸩).f.erase y = u.f := by
  cases u with
  | bound =>
    simp [HasOpen.open_, Channel.open, Channel.f]
    split_ifs <;> simp
  | free z =>
    simp only [f, Finset.mem_singleton, HasOpen.open_,
      Channel.open, Finset.erase_eq_self] at ⊢ hy
    exact hy

@[simp] lemma Finset.f_open_erase {k : Nat} {zs : Finset Channel} {y : FPName} (hy : y ∉ zs.f) :
  zs⸨k | #y⸩.f.erase y = zs.f := by
  ext x
  simp only [Finset.mem_erase, Finset.f, Finset.mem_biUnion, Finset.mem_image,
    HasOpen.open_, Finset.open]
  constructor
  · rintro ⟨hneq, _, ⟨u, hu, rfl⟩, hx⟩
    have h_erase : x ∈ (u⸨k | #y⸩).f.erase y := by simp [HasOpen.open_, hneq, hx]
    rw [Channel.f_open_erase] at h_erase
    · use u
    · intro hc
      apply hy
      simp only [Finset.f, Finset.mem_biUnion]
      use u
  · rintro ⟨u, hu, hx⟩
    have hyu : y ∉ u.f := by
      intro hc
      apply hy
      simp only [Finset.f, Finset.mem_biUnion]
      use u
    have hneq : x ≠ y := by
      rintro rfl
      exact hyu hx
    have h_erase : x ∈ (u⸨k | #y⸩).f.erase y := by
      rwa [Channel.f_open_erase hyu]
    refine ⟨hneq, _, ⟨u, hu, rfl⟩, ?_⟩
    exact (Finset.mem_erase.mp h_erase).2

@[simp] lemma Proc.f_open_erase {P : Proc} {y : FPName} {k : Nat} (hy : y ∉ P.f) :
  (P⸨k | #y⸩.f).erase y = P.f := by
  induction P generalizing k <;>
    simp only [f_nil, f_one, f_bot, f_tensor, f_parr, f_cut, f_par, f_selectL,
      f_selectR, f_amp, f_output, f_input, f_server, f_consume, f_duplicate,
      f_dispose, f_link, Finset.notMem_empty, Finset.notMem_union, Finset.union_assoc,
      Finset.erase_eq_of_notMem, Finset.erase_union_distrib, not_false_eq_true, open_nil,
      open_one, open_bot, open_tensor, open_parr, open_cut, open_par, open_selectL,
      open_selectR, open_amp, open_output, open_input, open_server, open_consume,
      open_duplicate, open_dispose, open_link] at hy ⊢
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | consume ih | duplicate ih | dispose ih =>
    rw [Channel.f_open_erase hy.1, ih hy.2]
  case server u zs P ih  =>
    rw [Channel.f_open_erase hy.1, Finset.f_open_erase hy.2.1, ih hy.2.2]
  case cut ih => exact ih hy
  case par ihP ihQ => rw [ihP hy.1, ihQ hy.2]
  case amp ihP ihQ => rw [Channel.f_open_erase hy.1, ihP hy.2.1, ihQ hy.2.2]
  case link => rw [Channel.f_open_erase hy.1, Channel.f_open_erase hy.2]

@[simp] lemma Proc.f_open_two_erase {P : Proc} {x y : FPName} {k : Nat}
  (hx : x ∉ P.f) (hy : y ∉ P.f) (hneq : x ≠ y) :
  ((P⸨k | #x, #y⸩.f).erase x).erase y = P.f := by
  simp only [HasOpenTwo.open_]
  change (P⸨k + 1 | #y⸩⸨k | #x⸩.f.erase x).erase y = P.f
  rw [Proc.f_open_erase, Proc.f_open_erase hy]
  intro h
  have h1 : (P⸨k + 1 | #y⸩.f).erase y = P.f := Proc.f_open_erase hy
  have h2 := Finset.mem_erase_of_ne_of_mem hneq h
  rw [h1] at h2
  contradiction

lemma Proc.not_mem_f_open {P : Proc} {y z : FPName}
  (hzy : z ≠ y) (hfz : z ∉ P.f) (hy : y ∉ P.f) :
  y ∉ P⸨#z⸩.f := by
  intro hc
  have h_erased := Finset.mem_erase.mpr ⟨hzy.symm, hc⟩
  rw [Proc.f_open_erase hfz] at h_erased
  exact hy h_erased

@[simp] lemma Channel.open_bound_zero {x : FPName} :
  ($0)⸨#x⸩ = (#x) := by simp [HasOpen.open_, Channel.open]

@[simp] lemma Channel.f_bound {i : Nat} :
  (Channel.bound i).f = ∅ := by simp [Channel.f]

@[simp] lemma Channel.close_free_self {x : FPName} :
  (#x)⟪x⟫ = (.bound 0) := by simp [HasClose.close_, Channel.close]

@[simp] lemma Channel.close_free_other {x y : FPName} (hneq : x ≠ y) :
  (#y)⟪x⟫ = (#y) := by simp_all [HasClose.close_, Channel.close]

@[simp] lemma Channel.close_self_bound {x : FPName} {i : Nat} :
  (Channel.bound i)⟪x⟫ = (.bound i) := by simp [HasClose.close_, Channel.close]

lemma Channel.close_not_mem {u : Channel} {z : FPName} {k : Nat} (h : z ∉ u.f) :
  u⟪k | z⟫ = u := by
  cases u <;>
    simp only [f, Finset.mem_singleton, HasClose.close_, close, beq_iff_eq, ite_eq_right_iff,
      reduceCtorEq, imp_false] at *
  case free f => apply h

lemma Finset.close_not_mem {zs : Finset Channel} {z : FPName} {k : Nat} (h : z ∉ zs.f) :
  zs⟪k | z⟫ = zs := by
  simp only [HasClose.close_, Finset.close]
  ext u
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨u, hin, rfl⟩
    have hzu : z ∉ u.f := by
      intro hc
      apply h
      simp only [Finset.f, Finset.mem_biUnion]
      use u
    change u⟪k | z⟫ ∈ zs
    rwa [Channel.close_not_mem (k := k) hzu]
  · intro hin
    have hzu : z ∉ u.f := by
      intro hc
      apply h
      simp only [Finset.f, Finset.mem_biUnion]
      use u
    exact ⟨u, hin, Channel.close_not_mem hzu⟩

lemma Proc.close_not_mem {P : Proc} {z : FPName} {k : Nat} (h : z ∉ P.f) :
  P⟪k | z⟫ = P := by
  induction P generalizing k <;> (
    simp only [Proc.f, Finset.mem_union, not_or] at h
    try simp only [close_nil, close_one, close_bot, close_tensor, close_parr, close_cut,
          close_par, close_selectL, close_selectR, close_amp, close_output, close_input,
          close_server, close_consume, close_duplicate, close_dispose, close_link, one.injEq,
          bot.injEq, tensor.injEq, parr.injEq, cut.injEq, par.injEq, selectL.injEq, selectR.injEq,
          amp.injEq, output.injEq, input.injEq, server.injEq, consume.injEq, duplicate.injEq,
          dispose.injEq, link.injEq, and_true]
  )
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
  | consume ih | dispose ih | duplicate ih => exact ⟨Channel.close_not_mem h.1, ih h.2⟩
  case server ih =>
    exact ⟨Channel.close_not_mem h.1.1, Finset.close_not_mem h.1.2, ih h.2⟩
  case cut ih => exact ih h
  case par ihP ihQ => exact ⟨ihP h.1, ihQ h.2⟩
  case amp ihP ihQ => exact ⟨Channel.close_not_mem h.1.1, ihP h.1.2, ihQ h.2⟩
  case link => exact ⟨Channel.close_not_mem h.1, Channel.close_not_mem h.2⟩

@[simp] lemma Channel.f_close {u : Channel} {x : FPName} {k : Nat} :
  (u⟪k | x⟫).f = u.f \ {x} := by
  cases u <;> simp only [f, HasClose.close_, close, beq_iff_eq, Finset.empty_sdiff]
  case free f =>
    split_ifs with heq
    case pos => subst heq ; simp
    case neg =>
      ext y
      simp_all only [← ne_eq, Finset.mem_singleton, Finset.mem_sdiff, iff_self_and]
      intro h
      subst h
      exact heq.symm

@[simp] lemma Finset.f_close {zs : Finset Channel} {x : FPName} {k : Nat} :
  (zs⟪k | x⟫).f = zs.f \ {x} := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_image,
    HasClose.close_, Finset.close, Finset.f]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hy⟩
    change y ∈ u⟪k | x⟫.f at hy
    rw [Channel.f_close] at hy
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hy
    exact ⟨⟨u, hu, hy.1⟩, hy.2⟩
  · rintro ⟨⟨u, hu, hy_in_u⟩, hy_neq_x⟩
    refine ⟨u.close x k, ⟨u, hu, rfl⟩, ?_⟩
    change y ∈ u⟪k | x⟫.f
    rw [Channel.f_close]
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hy_in_u, hy_neq_x⟩

@[simp] lemma Proc.f_close {P : Proc} {x : FPName} {k : Nat} :
  (P⟪k | x⟫).f = P.f \ {x} := by
  induction P generalizing k <;>
    simp_all [← Finset.erase_eq, Finset.erase_union_distrib]

lemma Channel.lc_le_any {u : Channel} {k i : Nat} (hle : i ≤ k) :
  u.lc i → u.lc k := by
  induction u
  case free => simp [Channel.lc]
  case bound => grind [Channel.lc]

lemma Finset.lc_le_any {zs : Finset Channel} {k i : Nat} (hle : i ≤ k) :
  zs.lc i → zs.lc k := by
  intro h
  intros z hin
  exact Channel.lc_le_any hle (h z hin)

lemma Proc.lc_le_any {P : Proc} {k n i : Nat} (hle : i ≤ k) :
  P.lc i n → P.lc k n := by
  induction P generalizing n k i
  case nil => simp only [Proc.lc, imp_self]
  case one ih | bot ih | selectL ih | selectR ih | input ih | consume ih
    | dispose ih =>
    simp only [Proc.lc, and_imp]
    intro hChan hProc
    constructor
    · exact Channel.lc_le_any hle hChan
    · exact ih hle hProc
  case server ih =>
    simp only [Proc.lc, and_imp]
    intro hChan hFin hProc
    split_ands
    · exact Channel.lc_le_any hle hChan
    · exact Finset.lc_le_any hle hFin
    · exact ih hle hProc
  case tensor ih | parr ih | duplicate ih =>
    simp only [Proc.lc, and_imp]
    intro hChan hProc
    constructor
    · exact Channel.lc_le_any hle hChan
    · exact ih (by simp [hle]) hProc
  case cut ih =>
    simp only [Proc.lc] at ⊢ ih
    intro hProc
    apply ih (by simp [hle]) hProc
  case par ihP ihQ =>
    simp only [Proc.lc, and_imp]
    intro hP hQ
    constructor
    · exact ihP hle hP
    · exact ihQ hle hQ
  case amp ihP ihQ =>
    simp only [Proc.lc, and_imp]
    intro hChan hP hQ
    split_ands
    · exact Channel.lc_le_any hle hChan
    · exact ihP hle hP
    · exact ihQ hle hQ
  case output ih =>
    simp only [Proc.lc, and_imp]
    intro hChan hProc hlc
    split_ands
    · exact Channel.lc_le_any hle hChan
    · exact ih hle hProc
    · exact hlc
  case link =>
    simp only [Proc.lc, and_imp]
    intro hx hy
    constructor
    · exact Channel.lc_le_any hle hx
    · exact Channel.lc_le_any hle hy

lemma Channel.lc_le {u : Channel} {k : Nat} :
  u.lc k → u.lc (k + 1) := by
  intro h
  exact (Channel.lc_le_any) (by simp) h

lemma Finset.lc_le {zs : Finset Channel} {k : Nat} :
  zs.lc k → zs.lc (k + 1) := by
  intro h
  exact (Finset.lc_le_any) (by simp) h

lemma Proc.lc_le {P : Proc} {k n : Nat} :
  P.lc k n → P.lc (k + 1) n := by
  intro h
  exact (Proc.lc_le_any) (by simp) h

@[simp] lemma Channel.lc_bound {k i : Nat} (hl : i < k) :
  Channel.lc k (.bound i) := by simp [Channel.lc, hl]

@[simp] lemma Channel.lc_close {u : Channel} {x : FPName} {k i : Nat} (hle : i ≤ k) :
  u.lc k → u⟪i | x⟫.lc (k + 1) := by
  induction u
  case free y =>
    intro h
    simp only [lc, HasClose.close_, close, beq_iff_eq]
    split_ifs
    case pos heq => subst heq ; grind
    case neg hneq => simp
  case bound i =>
    simp only [lc, HasClose.close_, close]
    grind only

@[simp] lemma Finset.lc_close {zs : Finset Channel} {x : FPName} {k i : Nat} (hle : i ≤ k) :
  zs.lc k → zs⟪i | x⟫.lc (k + 1) := by
  intro h v hv
  simp only [HasClose.close_, Finset.close, Finset.mem_image] at hv
  rcases hv with ⟨u, hu, rfl⟩
  exact Channel.lc_close hle (h u hu)

@[simp] lemma Proc.lc_close {P : Proc} {x : FPName} {n k i : Nat} (hle : i ≤ k) :
  P.lc k n → P⟪i | x⟫.lc (k + 1) n := by
  induction P generalizing n k i
  case nil => simp only [Proc.lc, close_nil, imp_self]
  case one ih | bot ih | selectL ih | selectR ih | input ih | consume ih | dispose ih =>
    simp only [lc, close_one, close_bot, close_selectL, close_selectR, close_input,
      close_consume, close_dispose, and_imp]
    intro hChan hProc
    constructor
    · exact Channel.lc_close hle hChan
    · apply ih hle hProc
  case server ih =>
    simp only [lc, close_server, and_imp]
    intro hChan hFin hProc
    split_ands
    · exact Channel.lc_close hle hChan
    · exact Finset.lc_close hle hFin
    · apply ih hle hProc
  case tensor ih | parr ih | duplicate ih =>
    simp only [lc, close_tensor, close_parr, close_duplicate, and_imp]
    intro hChan hProc
    constructor
    · exact Channel.lc_close hle hChan
    · exact ih (by simp [hle]) hProc
  case cut ih =>
    simp only [lc, close_cut] at ⊢ ih
    apply ih
    grind
  case par ihP ihQ =>
    simp only [lc, close_par, and_imp] at ⊢ ihP ihQ
    intro hP hQ
    constructor
    · exact ihP hle hP
    · exact ihQ hle hQ
  case amp ihP ihQ =>
    simp only [lc, close_amp, and_imp] at ⊢ ihP ihQ
    intro hChan hP hQ
    split_ands
    · exact Channel.lc_close hle hChan
    · exact ihP hle hP
    · exact ihQ hle hQ
  case output ih =>
    simp only [lc, close_output, and_imp] at ⊢ ih
    intro hChan hProc hType
    split_ands
    · exact Channel.lc_close hle hChan
    · exact ih hle hProc
    · exact hType
  case link =>
    simp only [Proc.lc, Proc.close_link, and_imp]
    intro hx hy
    constructor
    · exact Channel.lc_close hle hx
    · exact Channel.lc_close hle hy

lemma Channel.close_substNames_comm_gen {u : Channel} {x y z : FPName} {k : Nat}
  (hzx : z ≠ x) (hzy : z ≠ y) :
  u⟪k | z⟫{y // x} = u{y // x}⟪k | z⟫ := by
  cases u
  case free =>
    simp only [HasClose.close_, Channel.close, HasSubst.subst, Channel.subst, beq_iff_eq]
    split_ifs
    case pos h1 h2 => subst h1 h2 ; contradiction
    case neg h1 h2 => simp [h1]
    case pos h1 h2 => subst h2 ; simp [hzy]
    case neg h1 h2 => simp ; split_ifs ; rfl
  case bound =>
    simp [HasClose.close_, Channel.close, HasSubst.subst, Channel.subst]

lemma Finset.close_substNames_comm_gen {zs : Finset Channel} {x y z : FPName} {k : Nat}
  (hzx : z ≠ x) (hzy : z ≠ y) :
  zs⟪k | z⟫{y // x} = zs{y // x}⟪k | z⟫ := by
  simp only [HasClose.close_, HasSubst.subst, Finset.close, Finset.subst, Finset.image_image]
  apply Finset.image_congr
  intro u _
  exact Channel.close_substNames_comm_gen hzx hzy

lemma Proc.close_substNames_comm_gen {P : Proc} {x y z : FPName} {k : Nat}
  (hzx : z ≠ x) (hzy : z ≠ y) :
  P⟪k | z⟫{y // x} = P{y // x}⟪k | z⟫ := by
  induction P generalizing k <;>
    try simp only [ close_nil, substNames_nil, close_one, substNames_one, one.injEq, close_bot,
      substNames_bot, bot.injEq, close_tensor, substNames_tensor, tensor.injEq, close_parr,
      substNames_parr, parr.injEq, close_cut, substNames_cut, cut.injEq, close_par,
      substNames_par, par.injEq, close_selectL, substNames_oplus₁, selectL.injEq,
      close_selectR, substNames_oplus₂, selectR.injEq, close_amp, substNames_amp, amp.injEq,
      close_output, substNames_exists, output.injEq, and_true, close_input, substNames_forall,
      input.injEq, close_server, substNames_bang, server.injEq, close_consume, substNames_quest,
      consume.injEq, close_duplicate, substNames_c, duplicate.injEq, close_dispose, substNames_w,
       dispose.injEq, close_link, substNames_ax, link.injEq]
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.close_substNames_comm_gen hzx hzy, ih⟩
  case server ih =>
    split_ands
    · exact Channel.close_substNames_comm_gen hzx hzy
    · exact Finset.close_substNames_comm_gen hzx hzy
    · exact ih
  case cut ih => exact ih
  case par ihP ihQ => exact ⟨ihP, ihQ⟩
  case amp ihP ihQ => exact ⟨Channel.close_substNames_comm_gen hzx hzy, ⟨ihP, ihQ⟩⟩
  case link => simp only [Channel.close_substNames_comm_gen hzx hzy, and_self]

lemma Proc.close_substNames_comm {P : Proc} {x y z : FPName} (hzx : z ≠ x) (hzy : z ≠ y) :
  P⟪z⟫{y // x} = P{y // x}⟪z⟫ := Proc.close_substNames_comm_gen (k := 0) hzx hzy

lemma Proc.closeCut_substNames_comm {P : Proc} {x y z w : FPName}
  (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) :
  P⟪z, w⟫{y // x} = P{y // x}⟪z, w⟫ := by
  simp only [HasSubst.subst, HasCloseTwo.close_, zero_add]
  change P⟪1 | w⟫⟪z⟫{y // x} = P{y // x}⟪1 | w⟫⟪z⟫
  rw [Proc.close_substNames_comm_gen (k := 0) hzx hzy]
  rw [Proc.close_substNames_comm_gen (k := 1) hwx hwy]

lemma Channel.f_subset_open {u : Channel} {x : FPName} {k : Nat} :
  u.f ⊆ (u.open (#x) k).f := by
  cases u
  case free => simp only [Channel.f, Channel.open, subset_refl]
  case bound => simp only [f_bound, Finset.empty_subset]

lemma Finset.f_subset_open {zs : Finset Channel} {x : FPName} {k : Nat} :
  zs.f ⊆ (zs.open (#x) k).f := by
  intro y hy
  simp only [f, mem_biUnion, Channel.f, Finset.open, Channel.open, beq_iff_eq,
    mem_image, exists_exists_and_eq_and] at hy ⊢
  obtain ⟨a, ha, hy⟩ := hy
  use a
  constructor
  · exact ha
  · cases a
    case free => simp only [hy]
    case bound => simp only [notMem_empty] at hy

lemma Proc.f_subset_open_gen {P : Proc} {x : FPName} {k : Nat} :
  P.f ⊆ P⸨k | #x⸩.f := by
  induction P generalizing k <;>
    simp_all only [ HasOpen.open_, f, Channel.f, Proc.open, Channel.open,
      beq_iff_eq, f_nil, f_one, f_bot, f_tensor, f_parr, f_cut, f_par, f_selectL,
      f_selectR, f_amp, f_output, f_input, f_server, f_consume, f_duplicate, f_dispose,
      f_link, Finset.union_assoc, subset_refl]
  case one u _ ih | bot u _ ih | tensor u _ ih | parr u _ ih | selectL u _ ih | selectR u _ ih
    | output u _ _ ih | input u _ ih | consume u _ ih | duplicate u _ ih | dispose u _ ih =>
    cases u
    case free =>
      apply Finset.insert_subset_insert
      exact ih
    case bound => grind
  case par ih1 ih2 =>
    apply Finset.union_subset_union
    · exact ih1
    · exact ih2
  case amp u _ _ ih1 ih2 =>
    cases u
    case free =>
      simp only [Finset.singleton_union]
      apply Finset.insert_subset_insert
      apply Finset.union_subset_union
      · exact ih1
      · exact ih2
    case bound => grind
  case server u _ _ ih =>
    cases u
    case free =>
      simp only [Finset.singleton_union]
      apply Finset.insert_subset_insert
      apply Finset.union_subset_union
      · exact Finset.f_subset_open
      · exact ih
    case bound => grind [Finset.f_subset_open]
  case link u v =>
    cases u
    case free => cases v <;>
      simp only [Finset.union_empty, Finset.singleton_union,
      Finset.singleton_subset_iff, Finset.mem_insert, true_or, subset_refl]
    case bound =>
      cases v <;>
        simp only [Finset.union_singleton, insert_empty_eq, Finset.union_idempotent,
          Finset.singleton_subset_iff, Finset.mem_insert, true_or, Finset.empty_subset]

lemma Proc.f_subset_open {P : Proc} {x : FPName} :
  P.f ⊆ P⸨#x⸩.f := Proc.f_subset_open_gen (k := 0)

lemma Channel.open_rec_substNames {u : Channel} {x y z : FPName} {k : Nat} :
  (u⸨k | #z⸩){y // x} = u{y // x}⸨k | #(z{y // x})⸩ := by
  cases u <;>
    simp only [HasSubst.subst, subst, HasOpen.open_, Channel.open, beq_iff_eq, FPName.subst] <;>
    split_ifs <;> simp only [ite_eq_left_iff, ite_eq_right_iff]
  case pos h =>
    intro h'
    exfalso
    exact h' h
  case neg h =>
    intro h'
    exfalso
    exact h h'

lemma Finset.open_rec_substNames {zs : Finset Channel} {x y z : FPName} {k : Nat} :
  (zs⸨k | #z⸩){y // x} = zs{y // x}⸨k | #(z{y // x})⸩ := by
  simp only [HasOpen.open_, HasSubst.subst, Finset.open,
    Finset.subst, Finset.image_image]
  apply Finset.image_congr
  intro c _
  exact Channel.open_rec_substNames

lemma Proc.open_rec_substNames {P : Proc} {x y z : FPName} {k : Nat} :
  (P⸨k | #z⸩){y // x} = (P{y // x})⸨k | #(z{y // x})⸩ := by
  induction P generalizing k <;>
    simp [Channel.open_rec_substNames, Finset.open_rec_substNames, *]

lemma Proc.open_substNames {P : Proc} {x y z : FPName} :
  P⸨#z⸩{y // x} = (P{y // x})⸨#(z{y // x})⸩ := by
  exact Proc.open_rec_substNames

lemma Proc.open_two_substNames {P : Proc} {x y z w : FPName} :
  (P⸨#z, #w⸩){y // x} = (P{y // x})⸨#(z{y // x}), #(w{y // x})⸩ := by
  change (P⸨1 | #w⸩⸨0 | #z⸩){y // x} = _
  rw [Proc.open_rec_substNames]
  rw [Proc.open_rec_substNames]
  rfl

lemma Channel.subst_of_not_mem {u : Channel} {x y : FPName} (hnin : x ∉ u.f) :
  u{y // x} = u := by
  cases u
  case free =>
    simp only [Channel.f, Finset.mem_singleton,
      ← ne_eq, subst_free, free.injEq] at hnin ⊢
    exact FPName.subst_self_of_ne hnin.symm
  case bound => simp only [Channel.subst_bound]

lemma Finset.subst_of_not_mem {zs : Finset Channel} {x y : FPName} (hnin : x ∉ zs.f) :
  zs{y // x} = zs := by
  simp only [HasSubst.subst, Finset.subst]
  simp only [mem_biUnion, not_exists, not_and, Finset.f] at hnin
  rw [Finset.image_congr (g := fun u => u) _]
  · rw [Finset.image_id']
  · intro c hc
    apply Channel.subst_of_not_mem
    intro hx
    exact hnin c hc hx

-- FIXME: remove linter false and fix
set_option linter.flexible false in
lemma Proc.substNames_of_not_mem {P : Proc} {x y : FPName} (h : x ∉ P.f) :
  P{y // x} = P := by
  induction P <;> simp_all
  case one u P ih | bot u P ih | tensor u P ih | parr u P ih | selectL u P ih | selectR u P ih
    | output u P A ih | input u P ih | consume u P ih | duplicate u P ih
    | dispose u P ih | amp u P Q ihP ihQ =>
    cases u
    case free w =>
      simp_all [← ne_eq, Channel.f]
      rw [FPName.subst_self_of_ne h.1.symm]
    case bound i => simp
  case server u _ P ih =>
    cases u
    case free w =>
      simp_all [← ne_eq, Channel.f]
      rw [FPName.subst_self_of_ne h.1.symm, Finset.subst_of_not_mem h.2.1]
      exact ⟨rfl, rfl⟩
    case bound i =>
      constructor
      · simp
      · exact Finset.subst_of_not_mem h.2.1
  case link u v =>
    constructor
    · cases u
      case free w =>
        simp_all [← ne_eq, Channel.f]
        rw [FPName.subst_self_of_ne h.1.symm]
      case bound i => simp
    · cases v
      case free w =>
        simp_all [← ne_eq, Channel.f]
        rw [FPName.subst_self_of_ne h.2.symm]
      case bound i => simp

@[simp] lemma Finset.f_image_free (zs : Finset FPName) :
  (zs.image Channel.free).f = zs := by
  ext y
  simp only [Finset.f, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, ⟨z, hz, rfl⟩, hy⟩
    simp only [Channel.f, Finset.mem_singleton] at hy
    rwa [← hy] at hz
  · intro hy
    exact ⟨.free y, ⟨y, hy, rfl⟩, by simp [Channel.f]⟩
