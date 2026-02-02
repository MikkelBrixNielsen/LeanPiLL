import Mathlib.Data.List.Permutation
import Mathlib.Tactic
import PiLL.Framework.model.base

abbrev Atom := Nat
abbrev FTVar := Nat
abbrev BTVar := Nat

inductive TVar : Type
  | free    (x : FTVar)
  | bound   (x : BTVar)
deriving DecidableEq, Repr

inductive Types : Type where
  | atom        (a : Atom)
  | atomDual    (a : Atom)
  | var         (v : TVar)
  | varDual     (v : TVar)
  | one
  | bot
  | tensor      (A B : Types)
  | parr        (A B : Types)
  | oplus       (A B : Types)
  | amp         (A B : Types)
  | bang        (A : Types)
  | quest       (A : Types)
  | forall_     (A : Types)           -- Binds 1 Type Variable
  | exists_     (A : Types)           -- Binds 1 Type Variable
deriving DecidableEq, BEq, Repr

infixr:90 " ⨂ " => Types.tensor
infixr:90 " ⊕ " => Types.oplus
infixr:90 " ⅋ " => Types.parr
infixr:90 " & " => Types.amp

instance : One Types := ⟨Types.one⟩
instance : Bot Types := ⟨Types.bot⟩

prefix:95 "??" => Types.quest
prefix:95 "!!" => Types.bang

notation:max "∃․" A => Types.exist_ A
notation:max "∀․" A => Types.forall_ A

def openTVar (k : Nat) (u : TVar) : TVar → TVar
  | TVar.bound i => if i = k then u else TVar.bound i
  | v => v

def openType (k : Nat) (u : TVar) : Types → Types
  | .atom a => .atom a
  | .atomDual a => .atomDual a
  | .var v => .var (openTVar k u v)
  | .varDual v => .varDual (openTVar k u v)
  | .one => .one
  | .bot => .bot
  | .tensor A B => .tensor (openType k u A) (openType k u B)
  | .parr A B => .parr (openType k u A) (openType k u B)
  | .oplus A B => .oplus (openType k u A) (openType k u B)
  | .amp A B => .amp (openType k u A) (openType k u B)
  | .bang A => .bang (openType k u A)
  | .quest A => .quest (openType k u A)
  | .forall_ A => .forall_ (openType (k+1) u A)
  | .exists_ A => .exists_ (openType (k+1) u A)

def openType0 (u : TVar) (A : Types) : Types :=
  openType 0 u A

def lcTVar : Nat → TVar → Prop
  | _, .free _ => True
  | k, .bound i => i < k

def lcType : Nat → Types → Prop
  | _, .atom _      => True
  | _, .atomDual _  => True
  | k, .var v       => lcTVar k v
  | k, .varDual v   => lcTVar k v
  | _, .one         => true
  | _, .bot         => true
  | k, .tensor A B  => lcType k A ∧ lcType k B
  | k, .parr A B    => lcType k A ∧ lcType k B
  | k, .oplus A B   => lcType k A ∧ lcType k B
  | k, .amp A B     => lcType k A ∧ lcType k B
  | k, .bang A => lcType k A
  | k, .quest A => lcType k A
  | k, .forall_ A => lcType (k+1) A
  | k, .exists_ A => lcType (k+1) A

def lcType0 : Types → Prop := lcType 0

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

def Types.dual : Types → Types
  | .atom a       => .atomDual a
  | .atomDual a   => .atom a
  | .var v        => .varDual v
  | .varDual v    => .var v
  | .one          => .bot
  | .bot          => .one
  | .tensor A B   => .parr (dual A) (dual B)
  | .parr A B     => .tensor (dual A) (dual B)
  | .oplus A B    => .amp (dual A) (dual B)
  | .amp A B      => .oplus (dual A) (dual B)
  | .bang A       => .quest (dual A)
  | .quest A      => .bang (dual A)
  | .forall_ A    => .exists_ (dual A)
  | .exists_ A    => .forall_ (dual A)

postfix:max "ᗮ" => Types.dual

theorem Types.dual_neq (A : Types) : A ≠ Aᗮ := by
  cases A <;> simp [dual]

theorem Types.dual_inj (A B : Types) : Aᗮ = Bᗮ ↔ A = B := by
  induction A generalizing B <;> cases B <;> simp [Types.dual, *]

@[simp]
theorem Types.dual_involution (A : Types) : Aᗮᗮ = A := by
  induction A <;> simp [Types.dual, *]

def Types.linImpl (A B : Types) : Types := Aᗮ ⅋ B
infix:90 " ⊸ " => Types.linImpl

abbrev FPName := Nat
abbrev BPName := Nat

inductive Channel : Type where
  | free    (x : FPName)
  | bound   (x : BPName)
deriving DecidableEq, BEq, Repr

inductive Proc : Type where
  | nil
  | one         (x : Channel) (P : Proc)
  | bot         (x : Channel) (P : Proc)
  | tensor      (x : Channel) (P : Proc)                -- Binds 1 name
  | parr        (x : Channel) (P : Proc)                -- Binds 1 name
  | cut         (P : Proc)                              -- Binds 2 names
  | par         (P Q : Proc)
  | selectL     (x : Channel) (P : Proc)
  | selectR     (x : Channel) (P : Proc)
  | amp         (x : Channel) (P Q : Proc)
  | output      (x : Channel) (P : Proc) (A : Types)
  | input       (x : Channel) (P : Proc)                -- Binds 1 Type Variable
  | server      (x : Channel) (P : Proc)
  | consume     (x : Channel) (P : Proc)
  | duplicate   (x : Channel) (P : Proc)                -- Binds 1 name
  | dispose     (x : Channel) (P : Proc)
  | link        (x y : Channel)
deriving DecidableEq, BEq, Repr

def openChannel (k : Nat) (u : Channel) : Channel → Channel
  | Channel.bound i => if i = k then u else Channel.bound i
  | c => c

def openProc (k : Nat) (u : Channel) : Proc → Proc
  | .nil => .nil
  | .one x P => .one (openChannel k u x) (openProc k u P)
  | .bot x P => .bot (openChannel k u x) (openProc k u P)
  | .tensor x P => .tensor (openChannel k u x) (openProc (k+1) u P)
  | .parr x P => .parr (openChannel k u x) (openProc (k+1) u P)
  | .cut P => .cut (openProc (k+2) u P) -- FIXME: Does this need two channel names?
  | .par P Q => .par (openProc k u P) (openProc k u Q)
  | .server x P => .server (openChannel k u x) (openProc k u P)
  | .duplicate x P => .duplicate (openChannel k u x) (openProc (k+1) u P)
  | .consume x P => .consume (openChannel k u x) (openProc k u P)
  | .dispose x P => .dispose (openChannel k u x) (openProc k u P)
  | .selectL x P => .selectL (openChannel k u x) (openProc k u P)
  | .selectR x P => .selectR (openChannel k u x) (openProc k u P)
  | .amp x P Q => .amp (openChannel k u x) (openProc k u P) (openProc k u Q)
  | .output x P A => .output (openChannel k u x) (openProc k u P) A
  | .input x P => .input (openChannel k u x) (openProc k u P)
  | .link x y => .link (openChannel k u x) (openChannel k u y)

def openProc0 (u : Channel) (P : Proc) : Proc :=
  openProc 0 u P

def openProcCut (x y : Channel) (P : Proc) : Proc :=
  openProc 0 x (openProc 1 y P)

def openProcTVar (k : Nat) (u : TVar) : Proc → Proc
  | .nil => .nil
  | .one x P => .one x (openProcTVar k u P)
  | .bot x P => .bot x (openProcTVar k u P)
  | .tensor x P => .tensor x (openProcTVar k u P)
  | .parr x P => .parr x (openProcTVar k u P)
  | .cut P => .cut (openProcTVar k u P)
  | .par P Q => .par (openProcTVar k u P) (openProcTVar k u Q)
  | .selectL x P => .selectL x (openProcTVar k u P)
  | .selectR x P => .selectR x (openProcTVar k u P)
  | .amp x P Q => .amp x (openProcTVar k u P) (openProcTVar k u Q)
  | .output x P A => .output x (openProcTVar k u P) (openType k u A)
  | .input x P => .input x (openProcTVar (k+1) u P)
  | .server x P => .server x (openProcTVar k u P)
  | .consume x P => .consume x (openProcTVar k u P)
  | .duplicate x P => .duplicate x (openProcTVar k u P)
  | .dispose x P => .dispose x (openProcTVar k u P)
  | .link x y => .link x y

def openProcTVar0 (u : TVar) (P : Proc) : Proc :=
  openProcTVar 0 u P

def lcChannel : Nat → Channel → Prop
  | _, .free _ => True
  | k, .bound i => i < k

def lcProc : Nat → Nat → Proc → Prop
  | _, _, .nil => True
  | k, n, .one x P => lcChannel k x ∧ lcProc k n P
  | k, n, .bot x P => lcChannel k x ∧ lcProc k n P
  | k, n, .tensor x P => lcChannel k x ∧ lcProc (k+1) n P
  | k, n, .parr x P => lcChannel k x ∧ lcProc (k+1) n P
  | k, n, .cut P => lcProc (k+2) n P
  | k, n, .par P Q => lcProc k n P ∧ lcProc k n Q
  | k, n, .selectL x P => lcChannel k x ∧ lcProc k n P
  | k, n, .selectR x P => lcChannel k x ∧ lcProc k n P
  | k, n, .amp x P Q => lcChannel k x ∧ lcProc k n P ∧ lcProc k n Q
  | k, n, .output x P A => lcChannel k x ∧ lcProc k n P ∧ lcType n A
  | k, n, .input x P => lcChannel k x ∧ lcProc k (n+1) P
  | k, n, .server x P => lcChannel k x ∧ lcProc k n P
  | k, n, .consume x P => lcChannel k x ∧ lcProc k n P
  | k, n, .duplicate x P => lcChannel k x ∧ lcProc (k+1) n P
  | k, n, .dispose x P => lcChannel k x ∧ lcProc k n P
  | k, _, .link x y => lcChannel k x ∧ lcChannel k y

def lcProc0 : Proc → Prop := lcProc 0 0

def Channel.f : Channel → Finset FPName
  | .free x => {x}
  | .bound _ => {}

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

def closeChannel (k : Nat) (name : FPName) : Channel → Channel
  | .free x => if x = name then .bound k else .free x
  | .bound i => .bound i

def closeProc (k : Nat) (name : FPName) : Proc → Proc
  | .nil => .nil
  | .one x P => .one (closeChannel k name x) (closeProc k name P)
  | .bot x P => .bot (closeChannel k name x) (closeProc k name P)
  | .tensor x P => .tensor (closeChannel k name x) (closeProc (k+1) name P) -- Binder +1
  | .parr x P => .parr (closeChannel k name x) (closeProc (k+1) name P)     -- Binder +1
  | .cut P => .cut (closeProc (k+2) name P)                                 -- Binder +2
  | .par P Q => .par (closeProc k name P) (closeProc k name Q)
  | .selectL x P => .selectL (closeChannel k name x) (closeProc k name P)
  | .selectR x P => .selectR (closeChannel k name x) (closeProc k name P)
  | .amp x P Q => .amp (closeChannel k name x) (closeProc k name P) (closeProc k name Q)
  | .output x P A => .output (closeChannel k name x) (closeProc k name P) A
  | .input x P => .input (closeChannel k name x) (closeProc k name P)
  | .server x P => .server (closeChannel k name x) (closeProc k name P)
  | .consume x P => .consume (closeChannel k name x) (closeProc k name P)
  | .duplicate x P => .duplicate (closeChannel k name x) (closeProc (k+1) name P) -- Binder +1
  | .dispose x P => .dispose (closeChannel k name x) (closeProc k name P)
  | .link x y => .link (closeChannel k name x) (closeChannel k name y)












abbrev Env := List (Channel × Types)

-- abbrev Env.mk (x : Channel) (A : Types) := [(x, A)]
-- infixr:86 " ∶ " => Env.mk

abbrev Env.mk (x : FPName) (A : Types) := [(Channel.free x, A)]
infixr:86 " ∶ " => Env.mk

abbrev Env.merge (Γ Δ : Env) : Env := Γ ++ Δ
infixl:85 "‚ " => Env.merge

lemma Env.merge_unitL (Γ : Env) : ∅‚ Γ = Γ := by simp

lemma Env.merge_unitR (Γ : Env) : Γ‚ ∅ = Γ := by simp

lemma Env.merge_comm (Γ Δ : Env) : List.Perm (Γ‚ Δ) (Δ‚ Γ) := by
  exact List.perm_append_comm

lemma Env.merge_assoc (Γ Δ Ξ : Env) : Γ‚ Δ‚ Ξ = Γ‚ (Δ‚ Ξ) := by
  simp [Env.merge]

lemma Env.merge_rotate_left (Γ : Env) (x : Channel × Types) :
  (x :: Γ).Perm (Γ‚ [x]) := by
  symm ; apply List.perm_append_singleton

lemma Env.merge_swap (Γ : Env) (x y : Channel × Types) :
  List.Perm (x :: y :: Γ) (y :: x :: Γ) := by
  symm ; simpa using List.Perm.swap x y Γ



abbrev HyperEnv := List Env

abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ++ ℋ
infixl:55 " |ₕ " => HyperEnv.merge

instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

lemma HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

lemma HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : List.Perm (𝒢 |ₕ ℋ) (ℋ |ₕ 𝒢) := by
  exact List.perm_append_comm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp [HyperEnv.merge]

lemma HyperEnv.merge_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢).Perm (𝒢 ++ Γ) := by
  symm ; apply List.perm_append_singleton

lemma HyperEnv.merge_swap (𝒢 : HyperEnv) (Γ Δ : Env) :
  List.Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢) := by
  symm ; simpa using List.Perm.swap Γ Δ 𝒢











-- TODO: Notation to remove the .free everywhere
-- Env's only talk about free variables anyway so make implicit in mk
-- the same goes for Proc all bounds names are LN so never expliicitly mentioned


-- prefix:max "^" => Channel.free
notation:max P:max "⸨" x "⸩" => openProc0 (Channel.free x) P
notation:max P:max "⸨" x ", " y "⸩" => openProcCut (Channel.free x) (Channel.free y) P

notation:80 x "⟦⟧․" P:80 => Proc.one (Channel.free x) P
notation:80 x "⟦^⟧․" P:80 => Proc.tensor (Channel.free x) P
notation:80 x "⸨⸩․" P:80 => Proc.bot (Channel.free x) P
notation:80 x "⸨^⸩․" P:80 => Proc.parr (Channel.free x) P
notation:75 "𝑣⸨^, ""^⸩" P:80 => Proc.cut P
infixr:70 " |ₚ " => Proc.par
notation "𝟘" => Proc.nil




inductive Typing : Proc → HyperEnv → Prop where
  ------ Additional Structural and Exchange Rules ------

  -- | struct {P Q : Proc} {𝒢 ℋ : HyperEnv} :
  --     Typing P 𝒢 → P ≡ₚ Q → 𝒢.Perm ℋ →
  --     --------------------------------
  --     Typing Q ℋ

  -- | exchange_env {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} :
  --     Typing P (𝒢 |ₕ Γ) → Γ.Perm Δ →
  --     ------------------------------
  --     Typing P (𝒢 |ₕ Δ)

  -- | exchange_hyper {𝒢 ℋ : HyperEnv} {P : Proc} :
  --     Typing P 𝒢 → 𝒢.Perm ℋ →
  --     ------------------------
  --     Typing P ℋ

  ----------------- Actual Typing Rules -----------------

  | mix₀ :
      Typing 𝟘 ∅

  | mix {Ω 𝒢 ℋ : HyperEnv} {P Q : Proc} :
      Typing P 𝒢 → Typing Q ℋ → Ω.Perm (𝒢 |ₕ ℋ) →
      ---------------------------------------------
      Typing (P |ₚ Q) Ω

  | one {P : Proc} {x : FPName} :
      Typing P ∅ →
      ---------------------------------------------
      Typing (x⟦⟧․P) (x ∶ 1)

  | bot {Ω : HyperEnv} {Γ : Env} {P : Proc} {x : FPName} :
      Typing P Γ → Ω.Perm (Γ‚ x ∶ ⊥) →
      ------------------------------------------------
      Typing (x⸨⸩․P) Ω

  | cut {Ω 𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {A : Types} (L : Finset FPName) :
      ∀ x y, x ∉ L → y ∉ L → x ≠ y →
      Typing (P⸨x, y⸩) (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) → Ω.Perm (𝒢 |ₕ Γ‚ Δ) →
      --------------------------------------------------------------------
      Typing (𝑣⸨^, ^⸩P) Ω

  | tensor {Ω Γ Δ : Env} {P : Proc} {x : FPName} {B A : Types} (L : Finset FPName) :
      ∀ y, y ∉ L → Typing (P⸨y⸩) (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) →
      Ω.Perm (Γ‚ Δ‚ x ∶ A ⨂ B) →
      ----------------------------------------------------------------------
      Typing (x⟦^⟧․P) Ω

  | parr {Ω : HyperEnv} {Γ : Env} {P : Proc} {x : FPName} {A B : Types} (L : Finset FPName) :
      ∀ y, y ∉ L → Typing (P⸨y⸩) (Γ‚ y ∶ A‚ x ∶ B) → Ω.Perm (Γ‚ x ∶ A ⅋ B) →
      -----------------------------------------------------------------------
      Typing (x⸨^⸩․P) Ω

notation:65 "⊢ " P " ∷ " 𝒢 => Typing P 𝒢

-- lemma Typing.env_comm {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env} :
--   (⊢ P ∷ 𝒢 |ₕ Γ‚ Δ) → (⊢ P ∷ 𝒢 |ₕ Δ‚ Γ) :=
--   fun h => Typing.exchange_env h (Env.merge_comm _ _)

-- lemma Typing.env_rotateL {P : Proc} {𝒢 : HyperEnv} {Γ : Env} {x : Channel × Types} :
--   (⊢ P ∷ 𝒢 |ₕ Γ‚ [x]) → (⊢ P ∷ 𝒢 |ₕ {x :: Γ}) :=
--   fun h => Typing.exchange_env h (by symm ; apply Env.merge_rotate_left _ _)

-- lemma Typing.env_comm_singleton {P : Proc} {Γ Δ : Env} :
--   (⊢ P ∷ Γ‚ Δ) → (⊢ P ∷ Δ‚ Γ) :=
--   fun h => Typing.exchange_env (𝒢 := ∅) h (Env.merge_comm _ _)

-- lemma Typing.env_rotateL_singleton {P : Proc} {Γ : Env} {x : Channel × Types} :
--   (⊢ P ∷ Γ‚ [x]) → (⊢ P ∷ {x :: Γ}) :=
--   fun h => Typing.exchange_env (𝒢 := ∅) h (by symm ; apply Env.merge_rotate_left _ _)

-- lemma Typing.hyper_comm {P : Proc} {𝒢 ℋ : HyperEnv} :
--   (⊢ P ∷ 𝒢 |ₕ ℋ) → (⊢ P ∷ ℋ |ₕ 𝒢) :=
--   fun h => Typing.exchange_hyper h (HyperEnv.merge_comm _ _)











-- inductive TypingStep : {P : Proc} → {𝒢 : HyperEnv} → Typing P 𝒢 → Lbl →
--   {P' : Proc} → {𝒢' : HyperEnv} → Typing P' 𝒢' → Prop where
--   | one
--       {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ ∅} :
--       TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

--   | tensor
--       {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B} :
--       TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

--   | bot
--       {Γ : Env} {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ Γ} :
--       TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

--   | parr
--       {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A‚ x ∶ B} :
--       TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

--   | par₁
--       {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'} {ℰ : ⊢ Q ∷ ℋ}
--       (h : TypingStep 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
--       -----------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

--   | par₂
--       {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
--       {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h : TypingStep ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
--       ----------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

--   | syn
--       {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act}
--       {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'}
--       {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
--       (h₁ : TypingStep 𝒟 l 𝒟') (h₂ : TypingStep ℰ l' ℰ') :
--       ---------------------------------------------------------
--       TypingStep (Typing.mix 𝒟 ℰ) (l |ₗ l') (Typing.mix 𝒟' ℰ')

--   -- | alpha_equiv
--   --     {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
--   --     {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ 𝒢} {ℰ' : ⊢ Q' ∷ 𝒢'}
--   --     (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
--   --     -----------------------------------------------
--   --     TypingStep 𝒟 l ℰ'

--   | one_bot
--       {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
--       {𝒟 : ⊢ P ∷  𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥} {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ}
--       (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
--       -------------------------------------------------------
--       TypingStep (Typing.cut (Γ := ∅) 𝒟) (τ) 𝒟'

--   | tensor_parr
--       {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
--       {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ}
--       {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ x' ∶ A |ₕ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ}
--       (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
--       ----------------------------------------------------------------------------
--       TypingStep
--         (Typing.cut 𝒟)
--         (τ)
--         (Typing.cut (by
--           let inner := Typing.cut 𝒟'
--           rw [← Env.merge_assoc] at inner
--           exact inner
--           )
--         )

--   | res
--       {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
--       {x y : PName} {A : Types} {l : Lbl}
--       {𝒟 : Typing P (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ)}
--       {𝒟' : Typing P' (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ)}
--       (h : TypingStep 𝒟 l 𝒟') (disj : l.fresh [x, y]) :
--       --------------------------------------------------
--       TypingStep (Typing.cut 𝒟) l (Typing.cut 𝒟')










-- -- FIXME: Can't really read what is produced by the Typing.***_comm etc. lemmas
-- -- Make it look like the syntax
-- example : ⊢ ((10⟦⟧․𝟘) |ₚ (40⸨⸩․30⸨⸩․20⟦⟧․𝟘)) ∷
--   ((40 ∶ ⊥)‚ (30 ∶ ⊥)‚ 20 ∶ 1) |ₕ (10 ∶ 1) := by
--   apply Typing.hyper_comm
--   · apply Typing.mix
--     · apply Typing.one
--       apply Typing.mix₀
--     · apply Typing.env_rotateL_singleton
--       · apply Typing.bot
--         apply Typing.env_comm_singleton
--         · apply Typing.bot
--           · apply Typing.one
--             apply Typing.mix₀
