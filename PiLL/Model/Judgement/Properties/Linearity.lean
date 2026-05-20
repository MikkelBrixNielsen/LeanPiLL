import PiLL.Model.Judgement.Basic
import PiLL.Model.Environment.Lemmas
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.Processes.Fresh

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
      simp only [Env.disjoint] at ⊢ hDΓ
      intro x hxΔ hxa
      rw [← Env.names_eq_of_perm hP] at hxΔ
      exact le_trans (le_inf hxΔ hxa) (Disjoint.le_bot hDΓ)
    · exact ih.2
  case exchange_hyper hP ih =>
    rw [HyperEnv.PairwiseDisjoint, ← HyperEnv.Perm_PairwiseDisjoint_iff hP]
    exact ih

lemma Typing_preserves_linearity {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → HyperEnv.Nodup 𝒢 ∧ 𝒢.PairwiseDisjoint := by
  intro hT
  induction hT <;> try simp only [HyperEnv.Nodup_merge, HyperEnv.Nodup_singleton,
    HyperEnv.PairwiseDisjoint_merge, HyperEnv.PairwiseDisjoint_singleton, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq, Env.names_merge, Finset.disjoint_union_right,
    true_and, and_true, List.empty_eq, HyperEnv.Nodup_nil, HyperEnv.PairwiseDisjoint_nil,
    and_self, Env.Nodup_singleton]
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
    simp only [List.append_assoc, List.cons_append, List.nil_append, HyperEnv.Nodup_merge,
      HyperEnv.PairwiseDisjoint_merge, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, Env.names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Env.mem_pair_fst_in_names_iff, not_exists, forall_eq] at ih
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hNodup𝒢, hNodupxy⟩ := ih1
    obtain ⟨hPW𝒢, hPWxy, hGlue⟩ := ih2
    have hNodupΓ : Env.Nodup Γ :=
      (Env.Nodup_cons.mp (hNodupxy (x ∶ A :: Γ) (by simp))).2
    have hNodupΔ : Env.Nodup Δ :=
      (Env.Nodup_cons.mp (hNodupxy (y ∶ Aᗮ :: Δ) (by simp))).2
    refine ⟨⟨hNodup𝒢, ?_⟩, hPW𝒢, ?_⟩
    · simp only [Env.Nodup_merge_iff, Env.disjoint]
      refine ⟨hNodupΓ, hNodupΔ, ?_⟩
      have := HyperEnv.PairwiseDisjoint_implies_disjoint hPWxy
      simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
        Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff,
        not_exists, Finset.disjoint_insert_left, not_or] at this
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
      simp only [Env.names_merge, Finset.mem_union, Env.mem_pair_fst_in_names_iff, not_or,
        not_exists] ; constructor
      · exact Env.not_mem_names_iff.mp hF.1
      · exact Env.not_mem_names_iff.mp hF.2
    apply Env.Nodup_cons.mpr
    constructor
    · exact hFxΓΔ
    · simp only [Env.Nodup, List.map_append]
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
    simp only [HyperEnv.Nodup, List.mem_cons, List.not_mem_nil, or_false, Env.Nodup, forall_eq,
      List.map_cons, List.nodup_cons, List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
      not_exists, HyperEnv.PairwiseDisjoint_singleton, and_true] at ⊢ ih
    exact ih
  case c Γ _ x _ _ hF L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L)
    specialize ih y hy
    simp only [HyperEnv.Nodup, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      Env.names_distributes, Finset.singleton_union, Finset.mem_insert, Env.Nodup_cons,
      Env.mem_pair_fst_in_names_iff, not_or, not_exists, HyperEnv.PairwiseDisjoint_singleton,
      and_true] at ih ⊢
    exact ⟨ih.1.2, ih.2.2⟩
  case exists_ ih => simp_all [HyperEnv.Nodup, Env.Nodup]
  case forall_ Γ _ x B _ _ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have ih1' : Env.Nodup (x ∶ B :: Γ⁺) := ih1 _ (by simp)
    have hFx := (Env.Nodup_cons.mp ih1').1
    have hNodupΓ := (Env.Nodup_cons.mp ih1').2
    rw [Env.shiftTypes_preserves_names] at hFx
    rw [Env.Nodup_shiftTypes] at hNodupΓ
    rw [← HyperEnv.Nodup_singleton]
    have :=  (Env.Nodup_cons (A := B)).mpr ⟨hFx, hNodupΓ⟩
    simp only [Env.Nodup, List.map_cons, List.nodup_cons, List.mem_map, Prod.exists,
      exists_and_right, exists_eq_right, not_exists, HyperEnv.Nodup_singleton] at this ⊢
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
