import Mathlib.Data.List.Permutation
import Mathlib.Tactic

abbrev Atom := Nat

inductive Types : Type where
  | atom (a : Atom)
  | atomDual (a : Atom)
  | one
  | bot
  | tensor (A B : Types)
  | parr (A B : Types)

instance : One Types := ⟨Types.one⟩
instance : Bot Types := ⟨Types.bot⟩

infixr:90 " ⨂ " => Types.tensor
infixr:90 " ⅋ " => Types.parr


def Types.dual : Types → Types
  | atom a       => atomDual a
  | atomDual a   => atom a
  | one          => bot
  | bot          => one
  | tensor A B   => parr (dual A) (dual B)
  | parr A B     => tensor (dual A) (dual B)

postfix:max "ᗮ" => Types.dual

abbrev PName := Nat

inductive Proc : Type where
  | nil
  | one (x : PName) (P : Proc)
  | bot (x : PName) (P : Proc)
  | par (P Q : Proc)
  | cut (x y : PName) (P : Proc)
  | parr (x y : PName) (P : Proc)
  | tensor (x y : PName) (P : Proc)

notation:80 x "⟦" y "⟧․" P => Proc.tensor x y P
notation:80 x "⸨" y "⸩․" P => Proc.parr x y P
notation:80 x "⟦⟧․" P => Proc.one x P
notation:80 x "⸨⸩․" P => Proc.bot x P
notation:80 "𝑣⸨"x"," y"⸩"P => Proc.cut x y P
notation "𝟘" => Proc.nil
infixr:65 " |ₚ " => Proc.par

abbrev Env := List (PName × Types)

abbrev Env.mk (x : PName) (A : Types) := [(x, A)]
infixr:86 " ∶ " => Env.mk

abbrev Env.merge (Γ Δ : Env) : Env := Γ ++ Δ
infixl:85 "‚ " => Env.merge

abbrev HyperEnv := List Env

abbrev HyperEnv.merge (𝒢 ℋ : HyperEnv) : HyperEnv := 𝒢 ++ ℋ
infixl:55 " |ₕ " => HyperEnv.merge

instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

inductive Typing : Proc → HyperEnv → Prop where
  -- | struct {P Q : Proc} {𝒢 ℋ : HyperEnv} :
  --     Typing P 𝒢 → P ≡ₚ Q → 𝒢.Perm ℋ →
  --     --------------------------------
  --     Typing Q ℋ

  | exchange_env {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} :
      Typing P (𝒢 |ₕ Γ) → Γ.Perm Δ →
      ------------------------------
      Typing P (𝒢 |ₕ Δ)

  | exchange_hyper {𝒢 ℋ : HyperEnv} {P : Proc} :
      Typing P 𝒢 → 𝒢.Perm ℋ →
      ------------------------
      Typing P ℋ

  | mix₀ :
      Typing 𝟘 ∅

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} :
      Typing P 𝒢 → Typing Q ℋ →
      --------------------------
      Typing (P |ₚ Q) (𝒢 |ₕ ℋ)

  | one {P : Proc} {x : PName} :
      Typing P ∅ →
      ----------------------
      Typing (x⟦⟧․P) (x ∶ 1)

  | bot {Γ : Env} {P : Proc} {x : PName} :
      Typing P Γ →
      -------------------------
      Typing (x⸨⸩․P) (Γ‚ x ∶ ⊥)

  | cut {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {x y : PName} {A : Types} :
      Typing P (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) →
      -------------------------------------------
      Typing (𝑣⸨x, y⸩ P) (𝒢 |ₕ Γ‚ Δ)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types} :
      Typing P (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) →
      ---------------------------------
      Typing (x⟦y⟧․P) (Γ‚ Δ‚ x ∶ A ⨂ B)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
      Typing P (Γ‚ y ∶ A‚ x ∶ B) →
      ------------------------------
      Typing (x⸨y⸩․P) (Γ‚ x ∶ A ⅋ B)

notation:65 "⊢ " P " ∷ " 𝒢 => Typing P 𝒢




lemma Env.merge_unitL (Γ : Env) : ∅‚ Γ = Γ := by simp

lemma Env.merge_unitR (Γ : Env) : Γ‚ ∅ = Γ := by simp

lemma Env.merge_comm (Γ Δ : Env) : List.Perm (Γ‚ Δ) (Δ‚ Γ) := by
  exact List.perm_append_comm

lemma Env.merge_assoc (Γ Δ Ξ : Env) : Γ‚ Δ‚ Ξ = Γ‚ (Δ‚ Ξ) := by
  simp [Env.merge]

lemma Env.merge_rotate_left (Γ : Env) (x : PName × Types) :
  (x :: Γ).Perm (Γ‚ [x]) := by
  symm ; apply List.perm_append_singleton

lemma Env.merge_swap (Γ : Env) (x y : PName × Types) :
  List.Perm (x :: y :: Γ) (y :: x :: Γ) := by
  symm ; simpa using List.Perm.swap x y Γ

lemma HyperEnv.merge_unitL (𝒢 : HyperEnv) : ∅ |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_unitR (𝒢 : HyperEnv) : 𝒢 |ₕ ∅ = 𝒢 := by simp

lemma HyperEnv.merge_comm (𝒢 ℋ : HyperEnv) : List.Perm (𝒢 |ₕ ℋ) (ℋ |ₕ 𝒢) := by
  exact List.perm_append_comm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp [HyperEnv.merge]

lemma HyperEnv.rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢).Perm (𝒢 ++ Γ) := by
  symm ; apply List.perm_append_singleton

lemma HyperEnv.merge_swap (𝒢 : HyperEnv) (Γ Δ : Env) :
  List.Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢) := by
  symm ; simpa using List.Perm.swap Γ Δ 𝒢


lemma Typing.env_comm {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env} :
  (⊢ P ∷ 𝒢 |ₕ Γ‚ Δ) → (⊢ P ∷ 𝒢 |ₕ Δ‚ Γ) :=
  fun h => Typing.exchange_env h (Env.merge_comm _ _)

lemma Typing.env_rotateL {P : Proc} {𝒢 : HyperEnv} {Γ : Env} {x : PName × Types} :
  (⊢ P ∷ 𝒢 |ₕ Γ‚ [x]) → (⊢ P ∷ 𝒢 |ₕ {x :: Γ}) :=
  fun h => Typing.exchange_env h (by symm ; apply Env.merge_rotate_left _ _)

lemma Typing.env_comm_singleton {P : Proc} {Γ Δ : Env} :
  (⊢ P ∷ Γ‚ Δ) → (⊢ P ∷ Δ‚ Γ) :=
  fun h => Typing.exchange_env (𝒢 := ∅) h (Env.merge_comm _ _)

lemma Typing.env_rotateL_singleton {P : Proc} {Γ : Env} {x : PName × Types} :
  (⊢ P ∷ Γ‚ [x]) → (⊢ P ∷ {x :: Γ}) :=
  fun h => Typing.exchange_env (𝒢 := ∅) h (by symm ; apply Env.merge_rotate_left _ _)

lemma Typing.hyper_comm {P : Proc} {𝒢 ℋ : HyperEnv} :
  (⊢ P ∷ 𝒢 |ₕ ℋ) → (⊢ P ∷ ℋ |ₕ 𝒢) :=
  fun h => Typing.exchange_hyper h (HyperEnv.merge_comm _ _)



-- FIXME: Can't really read what is produced by the Typing.***_comm etc. lemmas
-- Make it look like the syntax
example : ⊢ ((10⟦⟧․𝟘) |ₚ (40⸨⸩․30⸨⸩․20⟦⟧․𝟘)) ∷
  ((40 ∶ ⊥)‚ (30 ∶ ⊥)‚ 20 ∶ 1) |ₕ (10 ∶ 1) := by
  apply Typing.hyper_comm
  · apply Typing.mix
    · apply Typing.one
      apply Typing.mix₀
    · apply Typing.env_rotateL_singleton
      · apply Typing.bot
        apply Typing.env_comm_singleton
        · apply Typing.bot
          · apply Typing.one
            apply Typing.mix₀






inductive Lbl : Type where
  | one (x : PName)
  | bot (x : PName)

inductive ProcStep : Proc → Lbl → Proc → Prop where


inductive EnvStep : Env → Lbl → Env → Prop where
