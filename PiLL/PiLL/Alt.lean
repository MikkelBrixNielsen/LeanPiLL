import Mathlib.Data.List.Permutation
import Mathlib.Tactic
import PiLL.Framework.model.base




-- De brujin Types and Proc relation needed






















abbrev Env := List (PName × Types)

abbrev Env.mk (x : PName) (A : Types) := [(x, A)]
infixr:86 " ∶ " => Env.mk

abbrev Env.merge (Γ Δ : Env) : Env := Γ ++ Δ
infixl:85 "‚ " => Env.merge

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

lemma HyperEnv.rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢).Perm (𝒢 ++ Γ) := by
  symm ; apply List.perm_append_singleton

lemma HyperEnv.merge_swap (𝒢 : HyperEnv) (Γ Δ : Env) :
  List.Perm (Γ :: Δ :: 𝒢) (Δ :: Γ :: 𝒢) := by
  symm ; simpa using List.Perm.swap Γ Δ 𝒢



inductive Typing : Proc → HyperEnv → Prop where
  ------ Additional Structural and Exchange Rules ------

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

  ----------------- Actual Typing Rules -----------------

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



inductive TypingStep : {P : Proc} → {𝒢 : HyperEnv} → Typing P 𝒢 → Lbl →
  {P' : Proc} → {𝒢' : HyperEnv} → Typing P' 𝒢' → Prop where
  | one
      {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ ∅} :
      TypingStep (Typing.one 𝒟) (x⟦⟧) 𝒟

  | tensor
      {Γ Δ : Env} {P : Proc} {x x': PName} {A B : Types}
      {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A |ₕ Δ‚ x ∶ B} :
      TypingStep (Typing.tensor 𝒟) (x⟦x'⟧) 𝒟

  | bot
      {Γ : Env} {P : Proc} {x : PName} {𝒟 : ⊢ P ∷ Γ} :
      TypingStep (Typing.bot 𝒟) (x⸨⸩) 𝒟

  | parr
      {Γ : Env} {P : Proc} {x x' : PName} {A B : Types}
      {𝒟 : ⊢ P ∷ Γ‚ x' ∶ A‚ x ∶ B} :
      TypingStep (Typing.parr 𝒟) (x⸨x'⸩) 𝒟

  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl}
      {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'} {ℰ : ⊢ Q ∷ ℋ}
      (h : TypingStep 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
      -----------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟' ℰ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl}
      {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
      (h : TypingStep ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
      ----------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) l (Typing.mix 𝒟 ℰ')

  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act}
      {𝒟 : ⊢ P ∷ 𝒢} {𝒟' : ⊢ P' ∷ 𝒢'}
      {ℰ : ⊢ Q ∷ ℋ} {ℰ' : ⊢ Q' ∷ ℋ'}
      (h₁ : TypingStep 𝒟 l 𝒟') (h₂ : TypingStep ℰ l' ℰ') :
      ---------------------------------------------------------
      TypingStep (Typing.mix 𝒟 ℰ) (l |ₗ l') (Typing.mix 𝒟' ℰ')

  -- | alpha_equiv
  --     {𝒢 𝒢' : HyperEnv} {P Q Q' : Proc} {l : Lbl}
  --     {𝒟 : ⊢ P ∷ 𝒢} {ℰ : ⊢ Q ∷ 𝒢} {ℰ' : ⊢ Q' ∷ 𝒢'}
  --     (h₁ : P =ₐ Q) (h₂ : TypingStep ℰ l ℰ') :
  --     -----------------------------------------------
  --     TypingStep 𝒟 l ℰ'

  | one_bot
      {𝒢: HyperEnv} {Γ : Env} {P P' : Proc} {x y : PName}
      {𝒟 : ⊢ P ∷  𝒢 |ₕ x ∶ 1 |ₕ Γ‚ y ∶ ⊥} {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ}
      (h : TypingStep 𝒟 (x⟦⟧ |ₗ y⸨⸩) 𝒟') :
      -------------------------------------------------------
      TypingStep (Typing.cut (Γ := ∅) 𝒟) (τ) 𝒟'

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {x y x' y' : PName} {A B : Types}
      {𝒟 : ⊢ P ∷ 𝒢 |ₕ Γ‚ Δ‚ x ∶ A ⨂ B |ₕ Ξ‚ y ∶ Aᗮ ⅋ Bᗮ}
      {𝒟' : ⊢ P' ∷ 𝒢 |ₕ Γ‚ x ∶ B |ₕ Δ‚ x' ∶ A |ₕ Ξ‚ y ∶ Bᗮ‚ y' ∶ Aᗮ}
      (h : TypingStep 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
      ----------------------------------------------------------------------------
      TypingStep
        (Typing.cut 𝒟)
        (τ)
        (Typing.cut (by
          let inner := Typing.cut 𝒟'
          rw [← Env.merge_assoc] at inner
          exact inner
          )
        )

  | res
      {𝒢 𝒢': HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc}
      {x y : PName} {A : Types} {l : Lbl}
      {𝒟 : Typing P (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ)}
      {𝒟' : Typing P' (𝒢' |ₕ Γ'‚ x ∶ A |ₕ Δ'‚ y ∶ Aᗮ)}
      (h : TypingStep 𝒟 l 𝒟') (disj : l.fresh [x, y]) :
      --------------------------------------------------
      TypingStep (Typing.cut 𝒟) l (Typing.cut 𝒟')










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



example : ⊢ 10⸨20⸩․10⸨⸩․20⟦⟧․𝟘 ∷ 10 ∶ 1 ⅋ ⊥ := by
  apply Typing.parr (Γ := ∅)
  apply Typing.bot
  apply Typing.one
  apply Typing.mix₀
