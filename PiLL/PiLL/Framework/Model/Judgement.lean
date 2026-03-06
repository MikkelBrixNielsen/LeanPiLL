import PiLL.Framework.Model.Environment
-- import PiLL.Framework.Model.Alpha
-- import PiLL.Framework.Model.Congruence

inductive Typing : Nat → Proc → HyperEnv → Prop where
  ----------------- Actual Typing Rules -----------------

  | mix₀ {n : Nat} :
      Typing n 𝟘 ∅

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {hD : 𝒢.disjoint ℋ} {n : Nat} :
      Typing n P 𝒢 → Typing n Q ℋ →
      ------------------------------
      Typing n (P |ₚ Q) (𝒢 |ₕ ℋ)

  | one {P : Proc} {x : FPName} {n : Nat} :
      Typing n P ∅ →
      ---------------------------
      Typing n (#x⟦⟧․P) [[x ∶ 1]]

  | bot {Γ : Env} {P : Proc} {x : FPName} {hF : x ∉ Γ.names} {n : Nat} :
      Typing n P [Γ] →
      ------------------------------
      Typing n (#x⸨⸩․P) [x ∶ ⊥ :: Γ]

  | cut {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {A : Types} {n : Nat} (L : Finset FPName) :
      (∀ x y, x ∉ L → y ∉ L → x ≠ y →
      Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])) →
      ----------------------------------------------------------
      Typing n (𝑣⸨$N,$N⸩P) (𝒢 |ₕ [Γ‚ Δ])

  | tensor {Γ Δ : Env} {P : Proc} {x : FPName} {A B : Types}
      {hF : x ∉ Γ.names ∧ x ∉ Δ.names} {n : Nat} (L : Finset FPName) :
      (∀ y, y ∉ L → Typing n (P⸨#y⸩) ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) →
      ---------------------------------------------------------------
      Typing n (#x⟦$N⟧․P) [x ∶ A ⨂ B :: Γ‚ Δ]

  | parr {Γ : Env} {P : Proc} {x : FPName} {A B : Types}
      {hF : x ∉ Γ.names} {n : Nat} (L : Finset FPName) :
      (∀ y, y ∉ L → Typing n (P⸨#y⸩) [y ∶ A :: x ∶ B :: Γ]) →
      -------------------------------------------------------
      Typing n (#x⸨$N⸩․P) [x ∶ A ⅋ B :: Γ]

  | oplus₁
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      B.lc n →
      Typing n P [x ∶ A :: Γ] →
      -----------------------------------
      Typing n (#x⟦𝐋⟧․P) [x ∶ A ⊕ B :: Γ]

  | oplus₂
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      A.lc n →
      Typing n P [x ∶ B :: Γ] →
      ------------------------------------
      Typing n (#x⟦𝐑⟧․P) [x ∶ A ⊕ B :: Γ]

  | amp
      {Γ : Env} {P Q : Proc} {x : FPName} {A B : Types} {n : Nat} :
      Typing n P [x ∶ A :: Γ] → Typing n Q [x ∶ B :: Γ] →
      ---------------------------------------------------
      Typing n (#x․case{𝐋 : P, 𝐑 : Q}) [x ∶ A & B :: Γ]

  | quest
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} :
      Typing n P [x ∶ A :: Γ] →
      -----------------------------------
      Typing n (#x⟦USE⟧․P) [x ∶ ??A :: Γ]

  | bang
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} :
      ?ₑΓ → Typing n P [x ∶ A :: Γ] →
      ---------------------------------
      Typing n (!#x․{P}) [x ∶ !!A :: Γ]

  | w
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {hF : x ∉ Γ.names} {n : Nat} :
      A.lc n → Typing n P [Γ] →
      -----------------------------------
      Typing n (#x⟦DISP⟧․P) [x ∶ ??A :: Γ]

  | c
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} (L : Finset FPName) :
      (∀ x', x' ∉ L →
      Typing n P⸨#x'⸩ [x ∶ ??A :: x' ∶ ??A :: Γ]) →
      --------------------------------------------
      Typing n (#x⟦DUP⟧⸨$N⸩․P) [x ∶ ??A :: Γ]

  | exists_
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      A.lc n →
      Typing n P [x ∶ B{A // 0} :: Γ] →
      ----------------------------------
      Typing n (#x⟦A⟧․P) [x ∶ ∃․B :: Γ]

  | forall_
      {Γ : Env} {P : Proc} {x : FPName} {B : Types} {n : Nat} :
      Typing (n + 1) P [x ∶ B :: Γ⁺ᵗ] →
      ----------------------------------
      Typing n (#x⸨$T⸩․P) [x ∶ ∀․B :: Γ]

  | ax
      {x y : FPName} {A : Types} {hneq : x ≠ y} {n : Nat} :
      A.lc n →
      Typing n (#x ⟷ₚ #y) [x ∶ Aᗮ :: [y ∶ A]]

  ------- Additional Structural / Exchange Rules -------

  | exchange_env {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {n : Nat} :
      Typing n P (Γ :: 𝒢) → Γ ~ Δ →
      -----------------------------
      Typing n P (Δ :: 𝒢)

  | exchange_hyper {𝒢 ℋ : HyperEnv} {P : Proc} {n : Nat} :
      Typing n P 𝒢 → 𝒢 ~ ℋ →
      -----------------------
      Typing n P ℋ

notation:50 n " ⊢ " P " ∷ " 𝒢 => Typing n P 𝒢

-- Projection of a Judgement to its process
def proc {𝒢 : HyperEnv} {P : Proc} {n : Nat} (_ : n ⊢ P ∷ 𝒢) : Proc := P

-- Projection of a Judgement to its environment
def env {𝒢 : HyperEnv} {P : Proc} {n : Nat} (_ : n ⊢ P ∷ 𝒢) : HyperEnv := 𝒢




-- FIXME: Get these working again
-- lemma Typing.env_comm {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env} :
--   (⊢ P ∷ 𝒢 |ₕ Γ‚ Δ) → (⊢ P ∷ 𝒢 |ₕ Δ‚ Γ) :=
--   fun h => Typing.exchange_env h (Env.merge_comm _ _)

-- lemma Typing.env_rotateL {P : Proc} {𝒢 : HyperEnv} {Γ : Env} {x : FPName × Types} :
--   (⊢ P ∷ 𝒢 |ₕ Γ‚ [x]) → (⊢ P ∷ 𝒢 |ₕ {x :: Γ}) :=
--   fun h => Typing.exchange_env h (by symm ; apply Env.merge_rotate_left _ _)

-- lemma Typing.env_comm_singleton {P : Proc} {Γ Δ : Env} :
--   (⊢ P ∷ Γ‚ Δ) → (⊢ P ∷ Δ‚ Γ) :=
--   fun h => Typing.exchange_env (𝒢 := ∅) h (Env.merge_comm _ _)

-- lemma Typing.env_rotateL_singleton {P : Proc} {Γ : Env} {x : FPName × Types} :
--   (⊢ P ∷ Γ‚ [x]) → (⊢ P ∷ {x :: Γ}) :=
--   fun h => Typing.exchange_env (𝒢 := ∅) h (by symm ; apply Env.merge_rotate_left _ _)

-- lemma Typing.hyper_comm {P : Proc} {𝒢 ℋ : HyperEnv} :
--   (⊢ P ∷ 𝒢 |ₕ ℋ) → (⊢ P ∷ ℋ |ₕ 𝒢) :=
--   fun h => Typing.exchange_hyper h (HyperEnv.merge_comm _ _)












theorem Typing_preserves_disjointness {P : Proc} {𝒢 : HyperEnv} {n : Nat}
  (h : n ⊢ P ∷ 𝒢) : 𝒢.PairwiseDisjoint := by
  induction h

  case mix₀ => constructor

  case mix hD _ _ _ ih𝒢 ihℋ =>
    rw [HyperEnv.PairwiseDisjoint, List.pairwise_append]
    refine ⟨ih𝒢, ihℋ, ?_⟩
    intros Γ hΓin𝒢 Δ hΔinℋ
    have hΓsub𝒢 := HyperEnv.subset_names_of_mem hΓin𝒢
    have hΔsubℋ := HyperEnv.subset_names_of_mem hΔinℋ
    exact Disjoint.mono hΓsub𝒢 hΔsubℋ hD

  case one => constructor <;> simp

  case bot | oplus₁ | oplus₂ | amp | quest | bang | w | exists_ | forall_=>
    constructor
    · intro a ha
      simp_all [HyperEnv.PairwiseDisjoint, Env.names]
    · simp

  case c L _ ih | tensor L _ ih | parr L _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    constructor
    · intro a ha
      simp_all [HyperEnv.PairwiseDisjoint, Env.names]
    · simp

  case ax hneq _ _ =>
    constructor <;> simp_all

  case cut L _ ih =>
    obtain ⟨u, v, hu, hv, hneq⟩ := exists_two_fresh L
    specialize ih u v hu hv hneq

    simp only [HyperEnv.PairwiseDisjoint, List.pairwise_append,
      List.pairwise_cons] at ih ⊢

    rcases ih with ⟨ih1, ih2, ih3⟩
    constructor
    · exact ih1.1
    · exact ⟨⟨by simp, by simp⟩, by simp_all [Env.names]⟩

  case exchange_env hP ih =>
    rw [HyperEnv.PairwiseDisjoint, List.pairwise_cons] at ⊢ ih
    constructor
    · intro a ha
      have hDΓ := ih.1 a ha
      simp [Env.disjoint] at ⊢ hDΓ
      intro x hxΔ hxa
      rw [← Env.names_eq_of_perm hP] at hxΔ
      exact le_trans (le_inf hxΔ hxa) (Disjoint.le_bot hDΓ)
    · exact ih.2

  case exchange_hyper hP ih =>
    rw [HyperEnv.PairwiseDisjoint, ← HyperEnv.Perm_pairwise_disjoint hP]
    exact ih

lemma Typing_preserves_lc {𝒢 : HyperEnv} {P : Proc} {n : Nat} :
  (n ⊢ P ∷ 𝒢) → ∀ Γ ∈ 𝒢, Γ.lc n := by
  intro hT E hE𝒢
  induction hT generalizing E

  case mix₀ => simp_all

  case mix =>
    simp at hE𝒢
    cases hE𝒢 <;> simp_all

  case one | bot | quest | bang | amp | oplus₁ | oplus₂ | w | ax =>
    simp_all [Env.lc_cons, Types.lc_dual.mp]
    simp_all [Env.lc, Types.lc]

  case exists_ Γ _ x A B n hlc _ ih =>
    simp at hE𝒢
    subst hE𝒢
    have h : Env.lc n ((x, B{A // 0}) :: Γ) := ih ((x, B{A // 0}) :: Γ) (by simp)
    rw [Env.lc_cons] at h ⊢
    exact ⟨(Types.lc_subst_inv_0 hlc).mp h.1, by simp_all⟩

  case forall_ Γ _ x B n _ ih =>
    simp at hE𝒢
    subst hE𝒢
    have h : Env.lc (n + 1) ((x, B) :: Γ⁺ᵗ) := ih ((x, B) :: Γ⁺ᵗ) (by simp)
    simp_all [Env.lc_cons]
    constructor
    · simp [Types.lc, h.1]
    · exact Env.lc_shift_inv_0.mp h.2

  case cut Γ Δ _ A n L _  ih =>
    obtain ⟨u, v, hu, hv, hneq⟩ := exists_two_fresh L
    specialize ih u v hu hv hneq
    simp at hE𝒢
    cases hE𝒢 with
    | inl => simp_all
    | inr hin =>
      subst hin
      have hΓ : Env.lc n ((u, A) :: Γ) := ih ((u, A) :: Γ) (by simp)
      have hΔ : Env.lc n ((v, Aᗮ) :: Δ) := ih ((v, Aᗮ) :: Δ) (by simp)
      rw [Env.lc_cons] at hΓ hΔ
      exact Env.lc_append.mpr ⟨hΓ.2, hΔ.2⟩

  case tensor L _ ih | parr L _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [Env.lc_cons]
    simp_all [Types.lc, Env.lc_append]

  case c L _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [Env.lc_cons]

  case exchange_env hP ih =>
    simp_all
    cases hE𝒢 with
    | inl => simp_all [(Env.lc_perm hP).mp]
    | inr => simp_all

  case exchange_hyper hP ih =>
    obtain ⟨Ξ, hin𝒢, hPΞ⟩ := HyperEnv.Perm_mem (Γ := E) hP hE𝒢
    exact (Env.lc_perm hPΞ).mp (ih Ξ hin𝒢)

lemma Typing_weakening {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  Typing n P 𝒢 → ∀ d c, Typing (n + c) (P ↑ᵗ d, c) (𝒢 ↑ᵗ d, c) := by
  intro h
  induction h <;> try simp_all ; intro d c

  case mix₀ => exact Typing.mix₀

  case mix hD _ _ ihP ihQ =>
    apply Typing.mix
    · simp ; exact hD
    · exact ihP d c
    · exact ihQ d c

  case ax hneq hlc =>
    rw [Types.shift_dual_comm_notation]
    apply Typing.ax
    · exact hneq
    · exact Types.lc_shift hlc

  case one ih =>
    exact Typing.one (ih d c)

  case bot hF _ ih =>
    exact Typing.bot (hF := by simp [hF]) (ih d c)

  case cut A _ L _ ih =>
    apply Typing.cut L (A := A ↑ᵗ d, c)
    intro x y hx hy hneq
    specialize ih x y hx hy hneq d c
    simp [← Types.shift_dual_comm_notation]
    rw [Proc.shiftTypes_openCut_comm] at ih
    exact ih

  case tensor L _ _ ih =>
    apply Typing.tensor L
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih
    · simp_all

  case parr L _ _ ih =>
    apply Typing.parr L
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih
    · simp_all

  case oplus₁ hlc _ ih =>
    apply Typing.oplus₁
    · exact Types.lc_shift hlc
    · exact ih d c

  case oplus₂ hlc _ ih =>
    apply Typing.oplus₂
    · exact Types.lc_shift hlc
    · exact ih d c

  case amp ihP ihQ =>
    exact Typing.amp (ihP d c) (ihQ d c)

  case quest ih =>
    exact Typing.quest (ih d c)

  case bang ih =>
    apply Typing.bang
    · simp_all
    · exact ih d c

  case w hlc _ ih =>
    apply Typing.w
    · simp_all
    · exact Types.lc_shift hlc
    · exact ih d c

  case c L _ ih =>
    apply Typing.c L
    intro x hx
    specialize ih x hx d c
    rw [Proc.shiftTypes_open0_comm] at ih
    exact ih

  case exists_ hlc _ ih =>
    apply Typing.exists_
    · exact Types.lc_shift hlc
    · simp [HasSubst.subst]
      rw [← Types.shift_subst_0_comm]
      exact ih d c

  case forall_ Γ Q x B n' hTQ ih =>
    apply Typing.forall_
    simp [HasShiftTypes.shift]
    rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc, Env.shiftTypes_comm]
    apply ih

  case exchange_env hP ih =>
    apply Typing.exchange_env
    · exact ih d c
    · simp_all

  case exchange_hyper hP ih =>
    intro d c
    apply Typing.exchange_hyper
    · exact ih d c
    · simp_all
