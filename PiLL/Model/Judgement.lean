import PiLL.Model.Environment
-- import PiLL.Model.Alpha
-- import PiLL.Model.Congruence

-- Same reason as in Environment.lean
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false

inductive Typing : Nat → Proc → HyperEnv → Prop where
  ----------------- Actual Typing Rules -----------------

  | mix₀ {n : Nat} :
      Typing n 𝟘 ∅

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {n : Nat} (hD : 𝒢.disjoint ℋ) :
      Typing n P 𝒢 → Typing n Q ℋ →
      ------------------------------
      Typing n (P |ₚ Q) (𝒢 |ₕ ℋ)

  | one {P : Proc} {x : FPName} {n : Nat} :
      Typing n P ∅ →
      ---------------------------
      Typing n (#x⟦⟧․P) [[x ∶ 1]]

  | bot {Γ : Env} {P : Proc} {x : FPName} {n : Nat} (hF : x ∉ Γ.names) :
      Typing n P [Γ] →
      ------------------------------
      Typing n (#x⸨⸩․P) [x ∶ ⊥ :: Γ]

  | cut {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {A : Types} {n : Nat} (L : Finset FPName) :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])) →
      ----------------------------------------------------------
      Typing n (𝑣⸨$N,$N⸩ P) (𝒢 |ₕ [Γ‚ Δ])

  | tensor {Γ Δ : Env} {P : Proc} {x : FPName} {A B : Types}
      {n : Nat} (hF : x ∉ Γ.names ∧ x ∉ Δ.names) (L : Finset FPName) :
      (∀ y ∉ L, Typing n (P⸨#y⸩) ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) →
      ---------------------------------------------------------------
      Typing n (#x⟦$N⟧․P) [x ∶ A ⨂ B :: Γ‚ Δ]

  | parr {Γ : Env} {P : Proc} {x : FPName} {A B : Types}
       {n : Nat} (hF : x ∉ Γ.names) (L : Finset FPName) :
      (∀ y ∉ L, Typing n (P⸨#y⸩) [y ∶ A :: x ∶ B :: Γ]) →
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
      -----------------------------------------------------------
      Typing n (!#x⟨Γ.names.image Channel.free⟩․{P}) [x ∶ !!A :: Γ]

  | w
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} (hF : x ∉ Γ.names) :
      A.lc n → Typing n P [Γ] →
      -----------------------------------
      Typing n (#x⟦DISP⟧․P) [x ∶ ??A :: Γ]

  | c
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat}
      (hF : x ∉ Γ.names) (L : Finset FPName) :
      (∀ x' ∉ L, Typing n P⸨#x'⸩ [x ∶ ??A :: x' ∶ ??A :: Γ]) →
      -------------------------------------------------------------
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
      {x y : FPName} {A : Types} {n : Nat} (hneq : x ≠ y):
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

  case mix hD _ _ ih𝒢 ihℋ =>
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
    specialize ih u hu v hv hneq

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
    rw [HyperEnv.PairwiseDisjoint, ← HyperEnv.Perm_PairwiseDisjoint_iff hP]
    exact ih

lemma Typing_preserves_lc_context {𝒢 : HyperEnv} {P : Proc} {n : Nat} :
  (n ⊢ P ∷ 𝒢) → ∀ Γ ∈ 𝒢, Γ.lc n := by
  intro hT E hE𝒢
  induction hT generalizing E

  case mix₀ => simp_all

  case mix =>
    simp at hE𝒢
    cases hE𝒢 <;> simp_all

  case one | bot | quest | bang | amp | oplus₁ | oplus₂ | w | ax =>
    simp_all [Env.lc_cons, Types.lc, Types.lc_dual.mp]

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
    specialize ih u hu v hv hneq
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

lemma Typing_preserves_lc_proc {𝒢 : HyperEnv} {P : Proc} {n : Nat}
  (hT : n ⊢ P ∷ 𝒢) : P.lc 0 n := by
  induction hT <;> try simp [Proc.lc, Channel.lc]

  case mix ihP ihQ => exact ⟨ihP, ihQ⟩

  case one ih | bot ih | oplus₁ ih | oplus₂ ih | quest ih | w ih | forall_ ih
    | exchange_env ih | exchange_hyper ih =>
    exact ih

  case bang ih =>
    simp [Finset.lc]
    constructor
    · intros z x T hx hxz
      rw [← hxz]
      simp [Channel.lc]
    · exact ih

  case cut L _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    exact Proc.lc_of_open_two (ih x hx y hy hneq)

  case amp ihP ihQ =>
    split_ands
    · exact ihP
    · exact ihQ

  case tensor L _ ih | parr L _ ih | c L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh L
    exact Proc.lc_of_open_gen (ih y hy)

  case exists_ hlc _ ih => exact ⟨ih, hlc⟩

lemma Typing_preserves_lc {𝒢 : HyperEnv} {P : Proc} {n : Nat}
  (hT : n ⊢ P ∷ 𝒢) : P.lc 0 n ∧ ∀ Γ ∈ 𝒢, Γ.lc n := by
  constructor
  · exact Typing_preserves_lc_proc hT
  · intro E hE𝒢 ; exact Typing_preserves_lc_context hT E hE𝒢

lemma Typing_weakening {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  Typing n P 𝒢 → ∀ d c, Typing (n + c) (P ↑ᵗ d, c) (𝒢 ↑ᵗ d, c) := by
  intro h
  induction h <;> try simp_all [Env.mem_pair_fst_in_names_iff] ; intro d c

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
    exact Typing.bot (hF := by simp [Env.mem_pair_fst_in_names_iff, hF]) (ih d c)

  case cut A _ L _ ih =>
    apply Typing.cut L (A := A ↑ᵗ d, c)
    intro x y hx hy hneq
    specialize ih x y hx hy hneq d c
    simp [← Types.shift_dual_comm_notation]
    rw [Proc.shiftTypes_openCut_comm] at ih
    exact ih

  case tensor L hF _ ih =>
    apply Typing.tensor (by simp_all [Env.mem_pair_fst_in_names_iff]) L
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih

  case parr L _ _ ih =>
    apply Typing.parr (by simp_all [Env.mem_pair_fst_in_names_iff]) L
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih

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
    rw [← Env.shiftTypes_preserves_names]
    apply Typing.bang
    · simp_all
    · exact ih d c

  case w hlc _ ih =>
    apply Typing.w
    · simp_all [Env.mem_pair_fst_in_names_iff]
    · exact Types.lc_shift hlc
    · exact ih d c

  case c L _ _ ih =>
    apply Typing.c (by simp_all [Env.mem_pair_fst_in_names_iff]) L
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

lemma Typing_preserves_linearity {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → HyperEnv.Nodup 𝒢 ∧ 𝒢.PairwiseDisjoint := by
  intro hT
  induction hT <;> try simp

  case mix hD _ _ ihP ihQ =>
    constructor
    · exact ⟨ihP.1, ihQ.1⟩
    · exact ⟨ihP.2, ihQ.2, HyperEnv.mem_of_disjoint hD⟩

  case bot hF _ ih | w hF _ _ ih =>
    rw [← HyperEnv.Nodup_singleton]
    apply (HyperEnv.Nodup_cons_iff hF).mpr
    exact ⟨by simp, ih.1⟩

  case cut Γ Δ _ A _ L _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    specialize ih x hx y hy hneq
    simp [HyperEnv.Nodup_merge] at ih
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hNodup𝒢, hNodupxy⟩ := ih1
    obtain ⟨hPW𝒢, hPWxy, hGlue⟩ := ih2

    have hNodupΓ : Env.Nodup Γ :=
      (Env.Nodup_cons.mp (hNodupxy (x ∶ A :: Γ) (by simp))).2

    have hNodupΔ : Env.Nodup Δ :=
      (Env.Nodup_cons.mp (hNodupxy (y ∶ Aᗮ :: Δ) (by simp))).2

    refine ⟨⟨hNodup𝒢, ?_⟩, hPW𝒢, ?_⟩
    · simp [Env.Nodup_merge_iff]
      refine ⟨hNodupΓ, hNodupΔ, ?_⟩
      have := HyperEnv.PairwiseDisjoint_implies_disjoint hPWxy
      simp at this
      exact this.2.2
    · intro a ha
      have := hGlue a ha
      exact ⟨this.1.2, this.2.2⟩

  case tensor Γ Δ _ x A B _ hF L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh L
    obtain ⟨ih1, ih2⟩ := ih y hy
    simp only [HyperEnv.Nodup_merge] at ih1

    have hNodupΓ : Env.Nodup Γ :=
      (Env.Nodup_cons.mp (ih1.1 (y ∶ A :: Γ) (by simp))).2

    have hNodupΔ : Env.Nodup Δ :=
      (Env.Nodup_cons.mp (ih1.2 (x ∶ B :: Δ) (by simp))).2

    have hDΓΔ : Disjoint Γ.names Δ.names := by
      have hDxy : Disjoint (Env.names (y ∶ A :: Γ)) (Env.names (x ∶ B :: Δ)) :=
        ((List.pairwise_cons.mp ih2).1) (x ∶ B :: Δ) (by simp)
      apply Disjoint.mono _ _ hDxy <;> simp

    have hFxΓΔ : x ∉ (Γ‚ Δ).names := by
      simp ; constructor
      · exact Env.not_mem_names_iff.mp hF.1
      · exact Env.not_mem_names_iff.mp hF.2

    apply Env.Nodup_cons.mpr
    constructor
    · exact hFxΓΔ
    · simp [Env.Nodup]
      rw [List.nodup_append]
      constructor
      · exact hNodupΓ
      · constructor
        · exact hNodupΔ
        · intro a ha b hb heq
          subst heq
          have haΓ : a ∈ Γ.names := by simp [Env.names, ha]
          have haΔ : a ∈ Δ.names := by simp [Env.names, hb]
          have hanΔ := Finset.disjoint_left.mp hDΓΔ haΓ
          contradiction

  case parr Γ _ x A B _ hF L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh L
    obtain ⟨ih1, ih2⟩ := ih y hy

    apply Env.Nodup_cons.mpr
    have := (Env.Nodup_cons.mp (ih1 (y ∶ A :: x ∶ B :: Γ) (by simp))).2
    exact (Env.Nodup_cons.mp this)

  case oplus₁ ih | oplus₂ ih | amp ih ih' | quest ih | bang ih =>
    simp [HyperEnv.Nodup, Env.Nodup] at ⊢ ih
    exact ih

  case c Γ _ x _ _ hF L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L)
    specialize ih y hy
    simp [HyperEnv.Nodup] at ih
    simp [Env.Nodup_cons] at ⊢ ih
    exact ⟨ih.1.2, ih.2.2⟩

  case exists_ ih => simp_all [HyperEnv.Nodup, Env.Nodup]

  case forall_ Γ _ x B _ _ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have ih1' : Env.Nodup (x ∶ B :: Γ⁺ᵗ) := ih1 _ (by simp)
    have hFx := (Env.Nodup_cons.mp ih1').1
    have hNodupΓ := (Env.Nodup_cons.mp ih1').2
    rw [Env.shiftTypes_preserves_names] at hFx
    rw [Env.Nodup_shiftTypes] at hNodupΓ
    rw [← HyperEnv.Nodup_singleton]
    have :=  (Env.Nodup_cons (A := B)).mpr ⟨hFx, hNodupΓ⟩
    simp [Env.Nodup] at this ⊢
    exact this

  case ax hneq _ => simp [Env.Nodup, hneq]

  case exchange_env hP ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · exact (HyperEnv.Nodup_cons_perm_iff hP).mp ih1
    · exact (HyperEnv.PairwiseDisjoint_cons_perm_iff hP).mp ih2

  case exchange_hyper hP ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · exact HyperEnv.Nodup_perm hP ih1
    · exact (HyperEnv.Perm_PairwiseDisjoint_iff hP).mp ih2

lemma Typing.f_eq_names {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → P.f = 𝒢.names := by
  intro h
  induction h <;> try simp [Channel.f]

  case mix ih1 ih2 => rw [ih1, ih2]

  case one ih | bot ih | oplus₁ ih | oplus₂ ih | bang ih | quest ih | w ih | exists_ ih
    | forall_ ih =>
    simp [ih]

  case cut ℋ Γ Δ P _ _ L _ ih =>
    have ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh (L ∪ P.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names)
    simp at hx hy ih
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have := ih x hx1 y hy1 hneq
    apply_fun (fun s => (s.erase y).erase x) at this
    rw [Finset.erase_insert (by simp [hy3, hneq.symm]), Finset.erase_insert (by simp [hx3]),
      Finset.erase_right_comm, Proc.f_open_two_erase hx2 hy2 hneq] at this
    exact this

  case tensor Γ Δ P x _ _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names ∪ Δ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case parr Γ P x _ _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case c Γ P x _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case amp ihP ihQ => simp [ihP, ihQ]

  case exchange_env hP ih =>
    simp [ih, Env.names_eq_of_perm hP]

  case exchange_hyper hP ih =>
    simp [ih, HyperEnv.names_eq_of_perm hP]

lemma Typing_inv_one {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⟦⟧․P) 𝒢) :
  (𝒢 ~ [[x ∶ 1]]) ∧ Typing n P ∅ := by
  generalize heq : (#x⟦⟧․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨h1, h2⟩ := ih heq
    have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
    exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨h1, h2⟩ := ih heq
    exact ⟨HyperEnv.Perm.trans hP.symm h1, h2⟩

  case one hT _ =>
    simp at heq
    constructor
    · simp [heq.1, HasPerm.perm]
    · simp [heq.2]
      exact hT

lemma Typing_inv_bot {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⸨⸩․P) 𝒢) :
  ∃ Γ, (𝒢 ~ [x ∶ ⊥ :: Γ]) ∧ Typing n P [Γ] := by
  generalize heq : (#x⸨⸩․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨Ξ, h⟩ := ih heq
    obtain ⟨h1, h2⟩ := h
    constructor
    · have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
      exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨Γ, h⟩ := ih heq
    obtain ⟨h1, h2⟩ := h
    constructor
    · exact ⟨HyperEnv.Perm.trans hP.symm h1, h2⟩

  case bot hT _ =>
    simp at heq
    constructor
    · constructor
      · simp [heq.1]
        apply HyperEnv.Perm.refl
      · simp [heq.2]
        exact hT

lemma Typing_inv_tensor {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⟦$N⟧․P) 𝒢) :
  ∃ (A B : Types) (Γ Δ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⨂ B :: Γ‚ Δ]) ∧ (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) := by
  generalize heq : (#x⟦$N⟧․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, Δ, L
    constructor
    · exact (HyperEnv.Perm.trans (hP'.symm) (HyperEnv.Perm.cons hP (HyperEnv.Perm.refl _))).symm
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, Δ, L
    constructor
    · exact HyperEnv.Perm.trans (hP.symm) hP'
    · exact hT'

  case tensor Γ Δ _ _ A B _ _ L hT _ =>
    simp at heq
    use A, B, Γ, Δ, L
    constructor
    · rw [heq.1]
    · rw [heq.1, heq.2]
      exact hT

lemma Typing_inv_parr {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⸨$N⸩․P) 𝒢) :
  ∃ (A B : Types) (Γ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⅋ B :: Γ]) ∧ (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: x ∶ B :: Γ])) := by
  generalize heq : (#x⸨$N⸩․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, B, Γ, L, hP', hT'⟩:= ih heq
    use A, B, Γ, L
    constructor
    · exact (HyperEnv.Perm.trans (hP'.symm) (HyperEnv.Perm.cons hP (HyperEnv.Perm.refl _))).symm
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨A, B, Γ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, L
    constructor
    · exact HyperEnv.Perm.trans (hP.symm) hP'
    · exact hT'

  case parr Γ _ _ A B _ _ L hT _ =>
    simp at heq
    use A, B, Γ, L
    constructor
    · rw [heq.1]
    · rw [heq.1, heq.2]
      exact hT

lemma Typing_inv_par {n : Nat} {P Q : Proc} {𝒢 : HyperEnv} (hT : n ⊢ P |ₚ Q ∷ 𝒢) :
  ∃ 𝒢₁ 𝒢₂, (𝒢 ~ 𝒢₁ |ₕ 𝒢₂) ∧ (n ⊢ P ∷ 𝒢₁) ∧ (n ⊢ Q ∷ 𝒢₂) ∧ Disjoint 𝒢₁.names 𝒢₂.names := by
  generalize heq : (P |ₚ Q) = PQ at hT
  induction hT generalizing P Q <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨ℋ₁, ℋ₂, hP', hT'⟩ := ih heq
    use ℋ₁, ℋ₂
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨ℋ₁, ℋ₂, hP', hT'⟩ := ih heq
    use ℋ₁, ℋ₂
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case mix 𝒢 ℋ _ _ _ hD hTP hTQ ihP ihQ =>
    simp at heq
    obtain ⟨hP, hQ⟩ := heq
    use 𝒢, ℋ
    rw [hP, hQ]
    exact ⟨by simp, hTP, hTQ, hD⟩

lemma Typing_inv_link {n : Nat} {x y : FPName} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟷ₚ#y ∷ 𝒢) :
  ∃ A, 𝒢 ~ [x ∶ Aᗮ :: [y ∶ A]] := by
  generalize heq : (#x⟷ₚ#y) = P at hT
  induction hT generalizing x y <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨T, hP'⟩ := ih heq
    use T
    exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm HyperEnv.Perm.rfl) hP'

  case exchange_hyper hP ih =>
    obtain ⟨T, hP'⟩ := ih heq
    use T
    exact HyperEnv.Perm.trans hP.symm hP'

  case ax A _ hneq hlc =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use A

lemma Typing_inv_amp {n : Nat} {x : FPName} {P Q : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x․case{𝐋 : P, 𝐑 : Q} ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A & B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) ∧ (n ⊢ Q ∷ [x ∶ B :: Γ]) := by
  generalize heq : (#x․case{𝐋 : P, 𝐑 : Q}) = PQ at hT
  induction hT generalizing P Q x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨𝒢', A, B, hP', hT'⟩ := ih heq
    use 𝒢', A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨𝒢', A, B, hP', hT'⟩ := ih heq
    use 𝒢', A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case amp Γ _ _ x A B _ hTP hTQ ihP ihQ =>
    simp at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_selectL {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦𝐋⟧․P ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A ⊕ B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) := by
  generalize heq : (#x⟦𝐋⟧․P) = PsL at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case oplus₁ Γ _ _ A B  _ hlc hPT ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_selectR {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦𝐑⟧․P ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A ⊕ B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ B :: Γ]) := by
  generalize heq : (#x⟦𝐑⟧․P) = PsR at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case oplus₂ Γ _ _ A B  _ hlc hPT ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_output {n : Nat} {x : FPName} {A : Types} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦A⟧․P ∷ 𝒢) :
  ∃ Γ B,
  (𝒢 ~ [x ∶ ∃․B :: Γ]) ∧ n ⊢ P ∷ [x ∶ B{A // 0} :: Γ] := by
  generalize heq : (#x⟦A⟧․P) = Pout at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case exists_ Γ _ _ _ B _ hlc hT ih =>
    simp at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    use Γ, B

lemma Typing_inv_input {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⸨$T⸩․P ∷ 𝒢) :
  ∃ (Γ : Env) (B : Types),
  (𝒢 ~ [x ∶ ∀․B :: Γ]) ∧ (n + 1 ⊢ P ∷ [x ∶ B :: Γ⁺ᵗ]) := by
  generalize heq : (#x⸨$T⸩․P) = Pin at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case forall_ Γ _ _ B _ _ ih  =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, B

lemma Typing_inv_use₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦USE⟧․P ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ ??A :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) := by
  generalize heq : (#x⟦USE⟧․P) = Puse at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env 𝒢 _ _ _ _ _ hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl 𝒢)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case quest Γ _ _ A _ _ ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_use₂ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ !#x․{P} ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ !!A :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) ∧ ?ₑΓ := by
  generalize heq : (!#x․{P}) = Puse at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env 𝒢 _ _ _ _ _ hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl 𝒢)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case bang Γ _ _ A _ _ _ _ =>
    simp at heq
    obtain ⟨rfl, _, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_disp₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦DISP⟧․P ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ ??A :: Γ]) ∧ (n ⊢ P ∷ [Γ]) ∧ x ∉ Env.names Γ := by
  generalize heq : (#x⟦DISP⟧․P) = Pdisp at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case w Γ _ _ A _ _ _ _ _ =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_dup₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦DUP⟧⸨$N⸩․P ∷ 𝒢) :
  ∃ (Γ : Env) (A : Types) (L : Finset FPName),
    (𝒢 ~ [x ∶ ??A :: Γ]) ∧ x ∉ Γ.names ∧
    (∀ x' ∉ L, x' ≠ x → n ⊢ P⸨#x'⸩ ∷ [x' ∶ ??A :: x ∶ ??A :: Γ]) := by
  generalize heq : (#x⟦DUP⟧⸨$N⸩․P) = Pdup at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, x', hP', hT'⟩ := ih heq
    use Γ, A, x'
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, x', hP', hT'⟩ := ih heq
    use Γ, A, x'
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case c Γ _ _ A _ hF L hT _ =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, L
    constructor
    · simp
    · constructor
      · exact hF
      · intros x' hin hneq
        apply Typing.exchange_hyper (hT x' hin)
        exact HyperEnv.Perm.cons (List.Perm.swap (x' ∶ ??A) (x ∶ ??A) Γ) (by simp)

lemma Typing_inv_res {n : Nat} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ 𝑣⸨$N,$N⸩ P ∷ 𝒢) :
  ∃ (A : Types) (Γ Δ : Env) (𝒢' : HyperEnv) (L : Finset FPName),
    (𝒢 ~ 𝒢' |ₕ [Γ‚ Δ]) ∧
    (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      n ⊢ P⸨#x, #y⸩ ∷ 𝒢' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) := by

  generalize heq : (𝑣⸨$N,$N⸩ P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, Γ, Δ, 𝒢, L, hP', hT'⟩ := ih heq
    use A, Γ, Δ, 𝒢, L
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (by rfl)) hP'
    · intros x hx y hy hneq
      exact hT' x hx y hy hneq

  case exchange_hyper hP ih =>
    obtain ⟨A, Γ, Δ, 𝒢, L, hP', hT'⟩ := ih heq
    use A, Γ, Δ, 𝒢, L
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · intros x hx y hy hneq
      exact hT' x hx y hy hneq

  case cut 𝒢 Γ Δ _ A _ L hT ih =>
    use A, Γ, Δ, 𝒢, L
    constructor
    · rfl
    · injection heq with heq
      subst heq
      intros x hx y hy hneq
      exact hT x hx y hy hneq
