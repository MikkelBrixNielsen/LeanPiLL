import PiLL.Framework.Model.STypes

-- abbrev PName := Nat

-- inductive Proc : Type where
--   | tensor    (x y : PName) (P : Proc)            -- x[y].P
--   | parr      (x y : PName) (P : Proc)            -- x(y).P
--   | one       (x : PName) (P : Proc)              -- x[].P
--   | bot       (x : PName) (P : Proc)              -- x().P
--   | cut       (x y : PName) (P : Proc)            -- 𝒗xy P
--   | par       (P Q : Proc)                        -- P | Q
--   | nil                                           -- 𝟘
--   | selectL   (x : PName) (P : Proc)              -- x[L].P
--   | selectR   (x : PName) (P : Proc)              -- x[R].P
--   | amp       (x : PName) (P Q : Proc)            -- x.case{L : P, R : Q}
--   | output    (x : PName) (P : Proc) (A : Types)  -- x[A].P
--   | input     (x : PName) (P : Proc) (X : TVar)   -- x(X).P
--   | server    (x : PName) (P : Proc)              -- !x.{P}
--   | consume   (x : PName) (P : Proc)              -- x[USE].P
--   | duplicate (x y : PName) (P : Proc)            -- x[DUP](y).P
--   | dispose   (x : PName) (P : Proc)              -- x[DISP].P
--   | link      (x y : PName)                       -- x ⟷ y
-- deriving DecidableEq

-- notation:80 x "⟦⟧․" P => (HasBracket.brack x () : Proc → Proc) P
-- notation:80 x "⟦"y"⟧․" P => (HasBracket.brack x y : Proc → Proc) P

-- instance : HasBracket PName Unit (Proc → Proc) where
--   brack x _ P := Proc.one x P
-- instance : HasBracket PName PName (Proc → Proc) where
--   brack x y := Proc.tensor x y
-- instance : HasBracket PName Types (Proc → Proc) where
--   brack x T P := Proc.output x P T

-- notation:80 x "⸨⸩․" P => (HasParen.paren x () : Proc → Proc) P
-- notation:80 x "⸨"y"⸩․" P => (HasParen.paren x y : Proc → Proc) P

-- instance : HasParen PName Unit (Proc → Proc) where
--   paren x _ P := Proc.bot x P
-- instance : HasParen PName PName (Proc → Proc) where
--   paren := Proc.parr
-- instance : HasParen PName TVar (Proc → Proc) where
--   paren x T P := Proc.input x P T

-- notation:75 "𝑣" "⸨" x ", " y "⸩ " P:80 => Proc.cut x y P
-- notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
-- notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
-- notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
-- notation:80 x "⟦DUP⟧⸨" y "⸩․" P:80 => Proc.duplicate x y P
-- notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
-- notation:80 "!" x "․{" P:80 "}" => Proc.server x P
-- notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

-- notation:80 x "⟷ₚ" y => Proc.link x y
-- infixr:70 " |ₚ " => Proc.par
-- notation "𝟘" => Proc.nil

-- private def reprProcAux : Proc → Nat → String
--   | .nil, _ => "𝟘"
--   | .tensor x y P, _ => s!"{x}⟦{y}⟧.{reprProcAux P 0}"
--   | .one x P, _ => s!"{x}⟦⟧.{reprProcAux P 0}"
--   | .parr x y P, _ => s!"{x}⸨{y}⸩.{reprProcAux P 0}"
--   | .bot x P, _ => s!"{x}⸨⸩.{reprProcAux P 0}"
--   | .cut x y P, _ => s!"𝑣⸨{x}, {y}⸩ {reprProcAux P 0}"
--   | .par P Q, _ => s!"({reprProcAux P 0} |ₚ {reprProcAux Q 0})"
--   | .selectL x P, _ => s!"{x}⟦𝐋⟧.{reprProcAux P 0}"
--   | .selectR x P, _ => s!"{x}⟦𝐑⟧.{reprProcAux P 0}"
--   | .amp x P Q, _ =>
--       s!"{x}:case" ++ "{" ++ s!" 𝐋 : {reprProcAux P 0}, 𝐑 : {reprProcAux Q 0}" ++ "}"
--   | .output x P A, _ => s!"{x}⟦{A}⟧.{reprProcAux P 0}"
--   | .input x P X, _ => s!"{x}⟦{X}⟧.{reprProcAux P 0}"
--   | .server x P, _ => s!"!{x}:" ++ "{" ++ s!"{reprProcAux P 0}" ++ "}"
--   | .consume x P, _ => s!"{x}⟦USE⟧.{reprProcAux P 0}"
--   | .duplicate x y P, _ => s!"{x}⟦DUP⟧⸨{y}⸩.{reprProcAux P 0}"
--   | .dispose x P, _ => s!"{x}⟦DISP⟧.{reprProcAux P 0}"
--   | .link x y, _ => s!"{x}⟷{y}"

-- instance : Repr Proc where
--   reprPrec P _ := reprProcAux P 0

-- instance : ToString Proc where
--   toString p := reprStr p

-- def Proc.f : Proc → Finset PName
--   | .tensor x y P         => {x} ∪ (P.f \ {y})
--   | .parr x y P           => {x} ∪ (P.f \ {y})
--   | .one x P              => {x} ∪ P.f
--   | .bot x P              => {x} ∪ P.f
--   | .cut x y P            => P.f \ {x, y}
--   | .par P Q              => P.f ∪ Q.f
--   | .nil                  => {}
--   | .selectL x P          => {x} ∪ P.f
--   | .selectR x P          => {x} ∪ P.f
--   | .amp x P Q            => {x} ∪ (P.f ∪ Q.f)
--   | .output x P _         => {x} ∪ P.f
--   | .input  x P _         => {x} ∪ P.f
--   | .server x P           => {x} ∪ P.f
--   | .consume x P          => {x} ∪ P.f
--   | .duplicate x y P      => {x} ∪ (P.f \ {y})
--   | .dispose x P          => {x} ∪ P.f
--   | .link x y             => {x, y}

-- def Proc.names : Proc → Finset PName
--   | .tensor x y P         => {x, y} ∪ P.names
--   | .parr x y P           => {x, y} ∪ P.names
--   | .one x P              => {x} ∪ P.names
--   | .bot x P              => {x} ∪ P.names
--   | .cut x y P            => {x, y} ∪ P.names
--   | .par P Q              => P.names ∪ Q.names
--   | .nil                  => {}
--   | .selectL x P          => {x} ∪ P.names
--   | .selectR x P          => {x} ∪ P.names
--   | .amp x P Q            => {x} ∪ (P.names ∪ Q.names)
--   | .output x P _         => {x} ∪ P.names
--   | .input  x P _         => {x} ∪ P.names
--   | .server x P           => {x} ∪ P.names
--   | .consume x P          => {x} ∪ P.names
--   | .duplicate x y P      => {x, y} ∪ P.names
--   | .dispose x P          => {x} ∪ P.names
--   | .link x y             => {x, y}

-- def Proc.boundNames (P : Proc) : Finset PName :=
--   P.names \ P.f

-- def Proc.substTypes (P : Proc) (A : Types) (X : TVar) : Proc :=
--   match P with
--   | .nil => .nil
--   | .one x P => .one x (P.substTypes A X)
--   | .bot x P => .bot x (P.substTypes A X)
--   | .tensor x y P => .tensor x y (P.substTypes A X)
--   | .parr x y P => .parr x y (P.substTypes A X)
--   | .cut x y P => .cut x y (P.substTypes A X)
--   | .par P Q => .par (P.substTypes A X) (Q.substTypes A X)
--   | .selectL x P => .selectL x (P.substTypes A X)
--   | .selectR x P => .selectR x (P.substTypes A X)
--   | .amp x P Q => .amp x (P.substTypes A X) (Q.substTypes A X)
--   | .server x P => .server x (P.substTypes A X)
--   | .dispose x P => .dispose x (P.substTypes A X)
--   | .duplicate x y P => .duplicate x y (P.substTypes A X)
--   | .consume x P => .consume x (P.substTypes A X)
--   | .link x y => .link x y
--   | .output x P B => .output x (P.substTypes A X) (B.subst A X)
--   | .input x P Y => if Y = X then .input x P Y else .input x (P.substTypes A X) Y

-- instance : HasSubst Proc Types TVar where subst := Proc.substTypes

-- def Proc.substName (P : Proc) (x z : PName) : Proc :=
--   let sub := fun (c : PName) => if c = z then x else c
--   match P with
--   | .nil => .nil
--   | .one a P => .one (sub a) (P.substName x z)
--   | .bot a P => .bot (sub a) (P.substName x z)
--   | .tensor a b P =>
--       if b = z then .tensor (sub a) b P
--       else .tensor (sub a) b (P.substName x z)
--   | .parr a b P =>
--       if b = z then .parr (sub a) b P
--       else .parr (sub a) b (P.substName x z)
--   | .cut a b P =>
--       if a = z ∨ b = z then .cut a b P
--       else .cut (sub a) (sub b) (P.substName x z)
--   | .par P Q => .par (P.substName x z) (Q.substName x z)
--   | .selectL a P => .selectL (sub a) (P.substName x z)
--   | .selectR a P => .selectR (sub a) (P.substName x z)
--   | .amp a P Q => .amp (sub a) (P.substName x z) (Q.substName x z)
--   | .server a P => .server (sub a) (P.substName x z)
--   | .dispose a P => .dispose (sub a) (P.substName x z)
--   | .duplicate a b P =>
--       if b = z then .duplicate (sub a) b P
--       else .duplicate (sub a) (sub b) (P.substName x z)
--   | .consume a P => .consume (sub a) (P.substName x z)
--   | .link a b => .link (sub a) (sub b)
--   | .output a P A => .output (sub a) (P.substName x z) A
--   | .input a P X => .input (sub a) (P.substName x z) X

-- instance : HasSubst Proc PName PName where subst := Proc.substName

-- @[simp]
-- lemma Proc.substName_par (P Q : Proc) (x z : PName) :
--   P{x // z} |ₚ Q{x // z} = (P |ₚ Q){x // z} := by rfl

-- @[simp] lemma Proc.substname_nil (x z : PName) : 𝟘{x // z} = 𝟘 := by
--   rfl

-- @[simp] lemma Proc.substName_link (a b x z : PName) :
--   (a⟷ₚb){x // z} = (if a = z then x else a)⟷ₚ(if b = z then x else b) := by
--   rfl

-- macro "solve_bound" : tactic =>
--   `(tactic| { simp [Proc.boundNames, Proc.names, Proc.f]; ext; simp; tauto })

-- @[simp] lemma Proc.boundNames_one (x : PName) (P : Proc) :
--   ((x⟦⟧․P).boundNames) = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_bot (x : PName) (P : Proc) :
--   ((x⸨⸩․P).boundNames) = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_selectL (x : PName) (P : Proc) :
--   (x⟦𝐋⟧․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_selectR (x : PName) (P : Proc) :
--   (x⟦𝐑⟧․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_amp (x : PName) (P Q : Proc) :
--   (x․case{𝐋 : P, 𝐑 : Q}).boundNames =
--   (P.boundNames ∪ Q.boundNames) \ (P.f ∪ Q.f ∪ {x}) := by solve_bound

-- @[simp] lemma Proc.boundNames_use (x : PName) (P : Proc) :
--   (x⟦USE⟧․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_bang (x : PName) (P : Proc) :
--   (!x․{P}).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_disp (x : PName) (P : Proc) :
--   (x⟦DISP⟧․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_dup (x y : PName) (P : Proc) :
--   (x⟦DUP⟧⸨y⸩․P).boundNames = (P.boundNames ∪ {y}) \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_output (x : PName) (A : Types) (P : Proc) :
--   (x⟦A⟧․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_input (x : PName) (A : TVar) (P : Proc) :
--   (x⸨A⸩․P).boundNames = P.boundNames \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_tensor (x y : PName) (P : Proc) :
--   (x⟦y⟧․P).boundNames = (P.boundNames ∪ {y}) \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_parr (x y : PName) (P : Proc) :
--   (x⸨y⸩․P).boundNames = (P.boundNames ∪ {y}) \ {x} := by solve_bound

-- @[simp] lemma Proc.boundNames_cut (x y : PName) (P : Proc) :
--   (𝑣⸨x, y⸩ P).boundNames = (P.boundNames ∪ {y, x}) := by solve_bound

-- @[simp] lemma Proc.f_subset_names (P : Proc) : P.f ⊆ P.names := by
--   induction P <;> simp only [Proc.f, Proc.names]

--   case nil | link | par | one | bot | selectL | selectR | amp | output
--     | input | server | consume | dispose => gcongr

--   case tensor ih | parr ih | duplicate ih =>
--     intro a ha
--     simp at ha ⊢
--     rcases ha with rfl | ⟨hf, _⟩
--     · left ; rfl
--     · right ; right ; apply ih ; exact hf

--   case cut ih =>
--     intro a ha
--     simp_all
--     apply ih ; exact ha.1

-- @[simp] lemma Proc.not_mem_names_not_bound_free (x : PName) (P : Proc) (h : x ∉ P.names) :
--   x ∉ P.boundNames ∪ P.f := by
--   simp only [Proc.boundNames, Finset.sdiff_union_self_eq_union, Finset.notMem_union]
--   apply And.intro
--   · exact h
--   · intro hf
--     apply h
--     apply Proc.f_subset_names
--     exact hf

-- lemma Proc.boundNames_par_subset_left (P Q : Proc) (x : PName)
--   (hxBP : x ∈ P.boundNames) (hNotQf : x ∉ Q.f) :
--   x ∈ (P |ₚ Q).boundNames := by
--   simp only [Proc.boundNames, Proc.names, Proc.f] at *
--   simp at hxBP
--   rcases hxBP with ⟨hxP, hxNotPf⟩
--   simp
--   apply And.intro
--   · left ; exact hxP
--   · simp [hxNotPf, hNotQf]

-- lemma Proc.not_bound_par_left {P Q : Proc} {x : PName}
--   (hSafe : x ∉ (P |ₚ Q).boundNames) (hNotQf : x ∉ Q.f) :
--   x ∉ P.boundNames := by
--   intro h_contra
--   apply hSafe
--   exact Proc.boundNames_par_subset_left P Q x h_contra hNotQf

-- lemma Proc.not_bound_par_right {P Q : Proc} {x : PName}
--   (hSafe : x ∉ (P |ₚ Q).boundNames) (hxNotPf : x ∉ P.f) :
--   x ∉ Q.boundNames := by
--   intro h_contra
--   apply hSafe
--   simp only [Proc.boundNames, Proc.names, Proc.f] at *
--   simp at h_contra
--   rcases h_contra with ⟨hxQ, hxNotQf⟩
--   simp
--   apply And.intro
--   · right ; exact hxQ
--   · simp [hxNotPf, hxNotQf]

-- @[simp] lemma Proc.substTypes_nil {A : Types} {X : TVar} : 𝟘{A // X} = 𝟘 := by rfl

-- @[simp] lemma Proc.substTypes_link {x y : PName} {A : Types} {X : TVar} :
--   (x⟷ₚy){A // X} = x⟷ₚy := by rfl

-- @[simp] lemma Proc.substTypes_par {P Q : Proc} {A : Types} {X : TVar} :
--   (P |ₚ Q){A // X} = P{A // X} |ₚ Q{A // X} := by rfl

-- @[simp] lemma Proc.substTypes_one {x : PName} {P : Proc} {A : Types} {X : TVar} :
--   (x⟦⟧․P){A // X} = x⟦⟧․(P{A // X}) := by rfl

-- @[simp] lemma Proc.substTypes_bot {x : PName} {P : Proc} {A : Types} {X : TVar} :
--   (x⸨⸩․P){A // X} = x⸨⸩․(P{A // X}) := by rfl

-- @[simp] lemma Proc.substTypes_output {x : PName} {P : Proc} {T A : Types} {X : TVar} :
--   (x⟦T⟧․P){A // X} = x⟦T{A // X}⟧․(P{A // X}) := by rfl


-- @[simp] lemma Proc.substTypes_input_match {x : PName} {P : Proc} {A : Types} {X : TVar} :
--   (x⸨X⸩․P){A // X} = x⸨X⸩․P := by
--   simp [HasSubst.subst, Proc.substTypes, HasParen.paren]

-- @[simp] lemma Proc.substTypes_input_diff {x : PName} {P : Proc} {A : Types} {X Y : TVar}
--   (hneq : Y ≠ X) : (x⸨Y⸩․P){A // X} = x⸨Y⸩․P{A // X} := by
--   simp_all [HasSubst.subst, Proc.substTypes, HasParen.paren]

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
notation:80 x "⟦#N⟧․" P => Proc.tensor x P
notation:80 x "⟦" A "⟧․" P => Proc.output x P A
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 x "⸨#N⸩․" P => Proc.parr x P
notation:80 x "⸨#T⸩․" P => Proc.input x P

notation:75 "𝑣⸨#,#⸩" P:80 => Proc.cut P
notation:80 x "⟦𝐋⟧․" P:80 => Proc.selectL x P
notation:80 x "⟦𝐑⟧․" P:80 => Proc.selectR x P
notation:80 x "⟦USE⟧․" P:80 => Proc.consume x P
notation:80 x "⟦DUP⟧⸨#N⸩․" P:80 => Proc.duplicate x P
notation:80 x "⟦DISP⟧․" P:80 => Proc.dispose x P
notation:80 "!" x "․{" P:80 "}" => Proc.server x P
notation:80 x "․case{𝐋" " : " P:80 ", " "𝐑" " : " Q :80"}" => Proc.amp x P Q

notation:80 x "⟷ₚ" y => Proc.link x y
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil

def Channel.open (k : Nat) (u : Channel) : Channel → Channel
  | Channel.bound i => if i = k then u else Channel.bound i
  | c => c

def Proc.open (k : Nat) (u : Channel) : Proc → Proc
  | .nil              => .nil
  | .one x P          => .one (Channel.open k u x) (.open k u P)
  | .bot x P          => .bot (Channel.open k u x) (.open k u P)
  | .tensor x P       => .tensor (Channel.open k u x) (.open (k + 1) u P)
  | .parr x P         => .parr (Channel.open k u x) (.open (k + 1) u P)
  | .cut P            => .cut (.open (k + 2) u P)
  | .par P Q          => .par (.open k u P) (.open k u Q)
  | .server x P       => .server (Channel.open k u x) (.open k u P)
  | .duplicate x P    => .duplicate (Channel.open k u x) (.open (k + 1) u P)
  | .consume x P      => .consume (Channel.open k u x) (.open k u P)
  | .dispose x P      => .dispose (Channel.open k u x) (.open k u P)
  | .selectL x P      => .selectL (Channel.open k u x) (.open k u P)
  | .selectR x P      => .selectR (Channel.open k u x) (.open k u P)
  | .amp x P Q        => .amp (Channel.open k u x) (.open k u P) (.open k u Q)
  | .output x P A     => .output (Channel.open k u x) (.open k u P) A
  | .input x P        => .input (Channel.open k u x) (.open k u P)
  | .link x y         => .link (Channel.open k u x) (Channel.open k u y)

def Proc.open0 (u : Channel) (P : Proc) : Proc :=
  Proc.open 0 u P
notation:max P:max "⸨" x "⸩" => Proc.open0 x P

def Proc.openCut (x y : Channel) (P : Proc) : Proc :=
  Proc.open 0 x (Proc.open 1 y P)
notation:max P:max "⸨" x ", " y "⸩" => Proc.openCut x y P

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

def lcChannel : Nat → Channel → Prop
  | _, .free _    => True
  | k, .bound i   => i < k

def lcProc : Nat → Nat → Proc → Prop
  | _, _, .nil              => True
  | k, n, .one x P          => lcChannel k x ∧ lcProc k n P
  | k, n, .bot x P          => lcChannel k x ∧ lcProc k n P
  | k, n, .tensor x P       => lcChannel k x ∧ lcProc (k + 1) n P
  | k, n, .parr x P         => lcChannel k x ∧ lcProc (k + 1) n P
  | k, n, .cut P            => lcProc (k + 2) n P
  | k, n, .par P Q          => lcProc k n P ∧ lcProc k n Q
  | k, n, .selectL x P      => lcChannel k x ∧ lcProc k n P
  | k, n, .selectR x P      => lcChannel k x ∧ lcProc k n P
  | k, n, .amp x P Q        => lcChannel k x ∧ lcProc k n P ∧ lcProc k n Q
  | k, n, .output x P A     => lcChannel k x ∧ lcProc k n P ∧ lcType n A
  | k, n, .input x P        => lcChannel k x ∧ lcProc k n P
  | k, n, .server x P       => lcChannel k x ∧ lcProc k n P
  | k, n, .consume x P      => lcChannel k x ∧ lcProc k n P
  | k, n, .duplicate x P    => lcChannel k x ∧ lcProc (k + 1) n P
  | k, n, .dispose x P      => lcChannel k x ∧ lcProc k n P
  | k, _, .link x y         => lcChannel k x ∧ lcChannel k y

def lcProc0 : Proc → Prop := lcProc 0 0

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
  | .free x   => if x = name then .bound k else .free x
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
