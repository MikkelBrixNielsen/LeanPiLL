import PiLL.Framework.Model.STypes

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
  | server      (x : Channel) (P : Proc)
  | consume     (x : Channel) (P : Proc)
  | duplicate   (x : Channel) (P : Proc)
  | dispose     (x : Channel) (P : Proc)
  | link        (x y : Channel)
deriving DecidableEq, BEq, Repr

notation:80 x "⟦⟧․" P => Proc.one x P
notation:80 x "⟦$N⟧․" P => Proc.tensor x P
notation:80 x "⟦" A "⟧․" P => Proc.output x P A
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 x "⸨$N⸩․" P => Proc.parr x P
notation:80 x "⸨$T⸩․" P => Proc.input x P

notation:75 "𝑣⸨$N,$N⸩" P:80 => Proc.cut P
notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
notation:80 x "⟦DUP⟧⸨$N⸩․" P:80 => Proc.duplicate x P
notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
notation:80 "!" x "․{" P:80 "}" => Proc.server x P
notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

notation:80 x "⟷ₚ" y => Proc.link x y
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil

def Channel.open (u v : Channel) (k : Nat) : Channel :=
  match u with
  | Channel.bound i => if i == k then v else Channel.bound i
  | c => c

instance : HasOpen Channel Channel Nat where open_ u v k := Channel.open u v k

def Proc.open (P : Proc) (u : Channel) (k : Nat) : Proc :=
  match P with
  | .nil              => .nil
  | .one x P          => .one (x.open u k) (P.open u k)
  | .bot x P          => .bot (x.open u k) (P.open u k)
  | .tensor x P       => .tensor (x.open u k) (P.open u (k + 1))
  | .parr x P         => .parr (x.open u k) (P.open u (k + 1))
  | .cut P            => .cut (P.open u (k + 2))
  | .par P Q          => .par (P.open u k) (Q.open u k)
  | .server x P       => .server (x.open u k) (P.open u k)
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

-- def openProcTVar (k : Nat) (u : TVar) : Proc → Proc
--   | .nil => .nil
--   | .one x P => .one x (openProcTVar k u P)
--   | .bot x P => .bot x (openProcTVar k u P)
--   | .tensor x P => .tensor x (openProcTVar k u P)
--   | .parr x P => .parr x (openProcTVar k u P)
--   | .cut P => .cut (openProcTVar k u P)
--   | .par P Q => .par (openProcTVar k u P) (openProcTVar k u Q)
--   | .selectL x P => .selectL x (openProcTVar k u P)
--   | .selectR x P => .selectR x (openProcTVar k u P)
--   | .amp x P Q => .amp x (openProcTVar k u P) (openProcTVar k u Q)
--   | .output x P A => .output x (openProcTVar k u P) (openType k u A)
--   | .input x P => .input x (openProcTVar (k+1) u P)
--   | .server x P => .server x (openProcTVar k u P)
--   | .consume x P => .consume x (openProcTVar k u P)
--   | .duplicate x P => .duplicate x (openProcTVar k u P)
--   | .dispose x P => .dispose x (openProcTVar k u P)
--   | .link x y => .link x y

-- def openProcTVar0 (u : TVar) (P : Proc) : Proc :=
--   openProcTVar 0 u P

def Channel.lc : Nat → Channel → Prop
  | _, .free _    => True
  | k, .bound i   => i < k

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
  | k, n, .input x P        => x.lc k ∧ P.lc k n
  | k, n, .server x P       => x.lc k ∧ P.lc k n
  | k, n, .consume x P      => x.lc k ∧ P.lc k n
  | k, n, .duplicate x P    => x.lc k ∧ P.lc (k + 1) n
  | k, n, .dispose x P      => x.lc k ∧ P.lc k n
  | k, _, .link x y         => x.lc k ∧ y.lc k

def Proc.lc_0 : Proc → Prop := Proc.lc 0 0

def Channel.f : Channel → Finset FPName
  | .free x     => {x}
  | .bound _    => {}

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
  | .server x P         => x.f ∪ P.f
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

def Channel.close (k : Nat) (name : FPName) : Channel → Channel
  | .free x   => if x == name then .bound k else .free x
  | .bound i  => .bound i

-- parr / tensor / duplicate binds 1
-- cut binds 2
def Proc.close (k : Nat) (name : FPName) : Proc → Proc
  | .nil => .nil
  | .one x P          => .one (Channel.close k name x) (Proc.close k name P)
  | .bot x P          => .bot (Channel.close k name x) (Proc.close k name P)
  | .tensor x P       => .tensor (Channel.close k name x) (Proc.close (k + 1) name P)
  | .parr x P         => .parr (Channel.close k name x) (Proc.close (k + 1) name P)
  | .cut P            => .cut (Proc.close (k + 2) name P)
  | .par P Q          => .par (Proc.close k name P) (Proc.close k name Q)
  | .selectL x P      => .selectL (Channel.close k name x) (Proc.close k name P)
  | .selectR x P      => .selectR (Channel.close k name x) (Proc.close k name P)
  | .amp x P Q        => .amp (Channel.close k name x) (Proc.close k name P) (Proc.close k name Q)
  | .output x P A     => .output (Channel.close k name x) (Proc.close k name P) A
  | .input x P        => .input (Channel.close k name x) (Proc.close k name P)
  | .server x P       => .server (Channel.close k name x) (Proc.close k name P)
  | .consume x P      => .consume (Channel.close k name x) (Proc.close k name P)
  | .duplicate x P    => .duplicate (Channel.close k name x) (Proc.close (k + 1) name P)
  | .dispose x P      => .dispose (Channel.close k name x) (Proc.close k name P)
  | .link x y         => .link (Channel.close k name x) (Channel.close k name y)

def Proc.shiftNames (d c : Nat) : Proc → Proc
  | .nil              => .nil
  | .one x P          => .one x (P.shiftNames d c)
  | .bot x P          => .bot x (P.shiftNames d c)
  | .tensor x P       => .tensor x (P.shiftNames (d + 1) c)
  | .parr x P         => .parr x (P.shiftNames (d + 1) c)
  | .cut P            => .cut (P.shiftNames (d + 2) c)
  | .par P Q          => .par (P.shiftNames d c) (Q.shiftNames d c)
  | .selectL x P      => .selectL x (P.shiftNames d c)
  | .selectR x P      => .selectR x (P.shiftNames d c)
  | .amp x P Q        => .amp x (P.shiftNames d c) (Q.shiftNames d c)
  | .output x P A     => .output x (P.shiftNames d c) A
  | .input x P        => .input x (P.shiftNames d c)
  | .server x P       => .server x (P.shiftNames d c)
  | .consume x P      => .consume x (P.shiftNames d c)
  | .duplicate x P    => .duplicate x (P.shiftNames (d + 1) c)
  | .dispose x P      => .dispose x (P.shiftNames d c)
  | .link x y         => .link x y

instance : HasShiftNames Proc where shift P d c := Proc.shiftNames d c P

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
  | .server x P       => .server x (P.shiftTypes d c)
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
  | .server x P       => .server (x.subst R T) (P.substNames R T)
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
  | .server x P       => .server x (P.substTypes A k)
  | .consume x P      => .consume x (P.substTypes A k)
  | .duplicate x P    => .duplicate x (P.substTypes A k)
  | .dispose x P      => .dispose x (P.substTypes A k)
  | .link x y         => .link x y

instance : HasSubst Proc Types Nat where subst P A k := Proc.substTypes A k P

@[simp] lemma FPName.subst_id {x z : FPName} :
  z{x // x} = z := by
  simp [HasSubst.subst, FPName.subst]
  intro h
  apply h.symm

@[simp] lemma FPName.subst_self {x y : FPName} :
  x{y // x} = y := by simp [HasSubst.subst, FPName.subst]

@[simp] lemma FPName.subst_self_of_ne {x y z : FPName} (hneq : z ≠ x) :
  z{y // x} = z := by
  simp [HasSubst.subst, FPName.subst]
  intro h
  contradiction

lemma FPName.subst_preserves_neq {w x y z : FPName}
  (hab : w ≠ z) (hya : y = w → y = x) (hyb : y = z → y = x) :
  w{y // x} ≠ z{y // x} := by
  simp only [HasSubst.subst, FPName.subst]
  split_ifs <;> simp_all
  all_goals {
    intro heq
    exact hya heq.symm
  }

@[simp] lemma Channel.subst_singleton_free {x y z : FPName} :
  (#z){y // x} = #(z{y // x}) := by
  simp [HasSubst.subst, Channel.subst, FPName.subst]
  split_ifs <;> simp

@[simp] lemma Channel.subst_self {u : Channel} {x : FPName} :
  u.subst x x = u := by
  induction u generalizing x <;> simp_all [Channel.subst]

@[simp] lemma Channel.subst_self_notation {u : Channel} {x : FPName} :
  u{x // x} = u := by
  induction u generalizing x <;> simp_all [HasSubst.subst, Channel.subst]

@[simp] lemma Proc.substNames_self {P : Proc} {x : FPName} :
  P{x // x} = P := by
  induction P generalizing x <;> simp_all [HasSubst.subst, Proc.substNames]

@[simp] lemma Proc.substNames_par {P Q : Proc} {x y : FPName} :
  (P |ₚ Q){y // x} = P{y // x} |ₚ (Q{y // x}) := by
  simp [HasSubst.subst, Proc.substNames]

macro "simp_Proc_substNames" : tactic =>
  `(tactic|
    (simp [HasSubst.subst, Proc.substNames, Channel.subst, FPName.subst] ;
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

@[simp] lemma Proc.substNames_bang {P : Proc} {u : Channel} {x y : FPName} :
  !u․{P}{y // x} = !u{y // x}․{P{y // x}} := by
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

@[simp] lemma Channel.open_subst_intro_gen (x : Channel) (k : Nat) {w z : FPName} (hF : w ∉ x.f) :
  x.open (#z) k = (x.open (#w) k){z // w} := by
  cases x with
  | bound i =>
    simp [Channel.open, HasSubst.subst, Channel.subst]
    split_ifs <;> simp
  | free f =>
    simp [Channel.open, HasSubst.subst, Channel.subst, Channel.f] at ⊢ hF
    intro h
    exfalso
    exact hF h.symm

lemma Proc.open_subst_intro_gen (P : Proc) (k : Nat) {w z : FPName} (hF : w ∉ P.f) :
  P⸨k | #z⸩ = P⸨k | #w⸩{z // w} := by
  induction P generalizing k <;> (
    try simp [Proc.f, HasOpen.open_, HasSubst.subst, Proc.open, Proc.substNames] at ⊢ hF
  )

  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih
    | input ih | server ih | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.open_subst_intro_gen _ _ hF.1, ih _ hF.2⟩

  case cut ih => apply ih _ hF
  case par ihP ihQ => exact ⟨ihP k hF.1, ihQ k hF.2⟩
  case amp ihP ihQ => exact ⟨Channel.open_subst_intro_gen _ _ hF.1, ihP _ hF.2.1, ihQ _ hF.2.2⟩
  case link => exact ⟨Channel.open_subst_intro_gen _ _ hF.1, Channel.open_subst_intro_gen _ _ hF.2⟩

lemma Proc.open_subst_intro {P : Proc} {w z : FPName} (hF : w ∉ P.f) :
  P⸨#z⸩ = P⸨#w⸩{z // w} := by
  exact Proc.open_subst_intro_gen P 0 hF

lemma Channel.open_substNames_comm_gen {u : Channel} {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  (u⸨k | #z⸩){y // x} = u{y // x}⸨k | #z⸩ := by
  induction u
  case free =>
    simp [HasOpen.open_, Channel.open, HasSubst.subst, Channel.subst]
    split_ifs <;> simp
  case bound =>
    simp [HasOpen.open_, Channel.open, HasSubst.subst, Channel.subst]
    split_ifs
    case pos => simp ; intro ; contradiction
    case neg => rfl

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

@[simp] lemma Proc.open_server {P : Proc} {u : Channel} {x : FPName} {k : Nat} :
  (!u․{P})⸨k | #x⸩ = !u⸨k | #x⸩․{P⸨k | #x⸩} := by
  simp [HasOpen.open_, Channel.open, Proc.open]

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

lemma Proc.open_substNames_comm_gen {P : Proc} {x y z : FPName} {k : Nat} (hneq : z ≠ x) :
  (P⸨k | #z⸩){y // x} = P{y // x}⸨k | #z⸩ := by
  induction P generalizing k <;> try simp

  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | server ih | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.open_substNames_comm_gen hneq, ih⟩

  case cut ih => exact ih
  case par ihP ihQ => exact ⟨ihP, ihQ⟩
  case amp ihP ihQ => exact ⟨Channel.open_substNames_comm_gen hneq, ⟨ihP, ihQ⟩⟩
  case link => simp [Channel.open_substNames_comm_gen hneq]

lemma Proc.open_substNames_comm {P : Proc} {x y z : FPName} (hF : z ≠ x) :
  (P⸨#z⸩){y // x} = (P{y // x})⸨#z⸩ := Proc.open_substNames_comm_gen (k := 0) hF

lemma Proc.openCut_substNames_comm {P : Proc} {x y z w : FPName}
  (hFz : z ≠ x) (hFw : w ≠ x) :
  P⸨#z, #w⸩{y // x} = P{y // x}⸨#z, #w⸩ := by
  simp [HasOpenTwo.open_, HasSubst.subst]
  change ((P⸨1 | #w⸩)⸨#z⸩){y // x} = P{y // x}⸨1 | #w⸩⸨#z⸩
  rw [Proc.open_substNames_comm_gen (k := 0) hFz]
  rw [Proc.open_substNames_comm_gen (k := 1) hFw]
