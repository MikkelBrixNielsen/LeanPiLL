import PiLL.Semantics.JudgementStep.Basic
import PiLL.Semantics.JudgementStep.Inversion.One
import PiLL.Semantics.JudgementStep.Inversion.Bot
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.One_Bot_Res

lemma TypingStepₘ_inv_one_bot_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  ∃ 𝒢ᵣ Γᵣ, (𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [Γᵣ]) := by
  generalize hl : (x⟦()⟧ |ₗ y⸨()⸩) = l at hStep
  induction hStep <;> try simp only [Lbl.par.injEq, reduceCtorEq] at hl
  case par₁ ih =>
    expose_names
    obtain ⟨𝒢', Γ', hP1, hP2⟩ := ih hl
    use (𝒢' |ₕ ℋ), Γ'
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right at hP1
      apply HyperEnv.Perm_rotate_rhs_left
      rw [← HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_right_inv hP1
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP2.trans HyperEnv.Perm.merge_comm
  case par₂ ih =>
    expose_names
    obtain ⟨ℋ', Γ', hP1, hP2⟩ := ih hl
    use (𝒢_1 |ₕ ℋ'), Γ'
    constructor
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      rw [HyperEnv.merge_assoc] at hP1
      exact HyperEnv.Perm_merge_cancel_left_inv hP1
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm_merge_cancel_left_inv hP2
  case syn 𝒥 𝒥' ℋ ℋ' Q Q' R R' l' l'' n' hD1 hD2 ℰ ℰ' ℱ ℱ' hSℰ hSℱ disj lwf ih1 ih2 =>
    rcases hl with ⟨rfl, rfl⟩
    obtain ⟨𝒥', hP𝒥1, hP𝒥2⟩ := TypingStepₘ_inv_one_existential hSℰ
    obtain ⟨ℋ', Γ', hPℋ1, hPℋ2⟩ := TypingStepₘ_inv_bot_existential hSℱ
    use 𝒥' |ₕ ℋ', Γ'
    constructor
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.trans (HyperEnv.Perm.merge hP𝒥1 hPℋ1)
      repeat rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      conv_rhs => rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm_merge_cancel_left_inv
      rw [List.append_eq, List.nil_append]
      apply HyperEnv.Perm_merge_singleton
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm.merge hP𝒥2 hPℋ2
  case res A _ l _ _ 𝒟 𝒟' u v hneq hu hv hu' hv' hlu hlv hStep ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    subst l
    simp only [Finset.union_assoc, Finset.mem_union, not_or, Lbl.f, fNamesAct,
      Finset.singleton_union, Lbl.i, iNamesAct, Finset.union_idempotent, Finset.union_empty,
      Finset.mem_insert, Finset.mem_singleton, ← ne_eq] at hu hv hu' hv' hlu hlv
    obtain ⟨hux, huy⟩ := hlu
    obtain ⟨hvx, hvy⟩ := hlv
    obtain ⟨_, hu𝒢, _, huΔ⟩ := hu
    obtain ⟨_, hv𝒢, hvΓ, _⟩ := hv
    obtain ⟨_, hu𝒢', _, _⟩ := hu'
    obtain ⟨_, hv𝒢', _, _⟩ := hv'
    exact HyperEnv.Perm.extract_one_bot_res
      hP1 hP2 hux.symm hvx.symm huy.symm hvy.symm hu𝒢 hv𝒢 hu𝒢' hv𝒢' hneq hvΓ huΔ
  case perm_hyper hP hP' _ ih =>
    obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := ih hl
    use 𝒢ᵣ, Γᵣ
    constructor
    · exact hP.symm.trans hP1
    · exact hP'.symm.trans hP2
  case perm_env 𝒢 ℋ Γ Γ' _ _ _ _ _ _ _ hP _ ih =>
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ih ⊢
    have ⟨𝒥, Ξ, hP1, hP2⟩ := ih hl
    use 𝒥, Ξ
    constructor
    · have : Γ' :: 𝒢 ~ Γ :: 𝒢 := by
        apply HyperEnv.Perm.cons hP.symm (by rfl)
      exact this.trans hP1
    · exact hP2

lemma TypingStepₘ_inv_one_bot_source {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x y : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  A = 1 ∧ B = ⊥ ∧ Γ = ∅ ∧ 𝒢' ~ 𝒢 |ₕ [∅‚ Δ] := by
  obtain ⟨𝒢ᵣ, Γᵣ, hP1, hP2⟩ := TypingStepₘ_inv_one_bot_existential hStep
  have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
  have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟
  have hxLHS : [x ∶ 1] ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] := by
    have hxRHS : [x ∶ 1] ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP1 hxRHS
    simp only [HasPerm.perm, List.perm_singleton] at hPΞ
    subst hPΞ
    exact hΞ
  simp only [List.append_assoc, List.cons_append, List.nil_append, HyperEnv.PairwiseDisjoint_merge,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Env.names_distributes,
    Finset.singleton_union, Finset.disjoint_insert_right, Env.mem_pair_fst_in_names_iff, not_exists,
    forall_eq] at hpw
  have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1
  have hyLHS : ∃ Γ', Γ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Γ' ~ y ∶ ⊥ :: Γᵣ := by
    have hyRHS : (y ∶ ⊥ :: Γᵣ) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γᵣ] := by simp
    have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP1 hyRHS
    simp only [HasPerm.perm] at hPΞ
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hΞ
    rcases hΞ with h1 | h2 | h3
    · exfalso
      exact (HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ ⊥ h1)
        ((List.Perm.mem_iff (a := y ∶ ⊥) hPΞ.symm).mp (by simp))
    · subst h2
      have hyin := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      simp only [List.mem_cons, Prod.mk.injEq] at hyin
      rcases hyin with ⟨rfl, rfl⟩ | h
      · exfalso ; simp at hDΓΔ
      · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
    · subst h3
      have hyin := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      simp only [List.mem_cons, Prod.mk.injEq, true_and] at hyin
      rcases hyin with rfl | h
      · refine ⟨(y ∶ ⊥ :: Δ), by simp, hPΞ⟩
      · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ h)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
    List.cons.injEq, Prod.mk.injEq, true_and, List.nil_eq, List.not_mem_nil,
    or_false] at hxLHS hyLHS
  rcases hxLHS with h1 | h2 | h3
  · exfalso
    apply HyperEnv.not_mem_names_iff.mp hx𝒢 [x ∶ 1] 1 h1
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  · rcases h2 with ⟨rfl, rfl⟩
    · have ⟨Ξ, hΞ, hPΞ⟩ := hyLHS
      have hyΞ := (List.Perm.mem_iff (a := y ∶ ⊥) hPΞ).mpr (by simp)
      rcases hΞ with h4 | h5 | h6
      · exfalso
        exact HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ ⊥ h4 hyΞ
      · subst h5
        simp [HasPerm.perm] at hPΞ
      · subst h6
        simp only [List.mem_cons, Prod.mk.injEq, true_and] at hyΞ
        rcases hyΞ with rfl | h2
        · have hPΞ' := hPΞ
          simp only [HasPerm.perm, List.perm_cons, List.empty_eq, List.nil_append,
            true_and] at ⊢ hPΞ'
          apply HyperEnv.Perm_singleton_singleton.mpr at hPΞ'
          apply HyperEnv.Perm_singleton_singleton.mpr at hPΞ
          have hP1': 𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Δ] :=
            hP1.trans (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hPΞ.symm)
          apply HyperEnv.Perm_merge_cancel_right at hP1'
          apply HyperEnv.Perm_merge_cancel_right at hP1'
          exact hP2.trans (HyperEnv.Perm.merge hP1'.symm hPΞ'.symm)
        · exfalso ; apply hyΔ
          exact Env.mem_pair_fst_in_names _ h2
  · obtain ⟨⟨rfl, _⟩, _⟩ := h3
    simp at hDΓΔ

lemma TypingStepₘ_inv_one_bot {n n' : Nat} {P P' : Proc} {𝒢ᵣ 𝒢' : HyperEnv}
  {x y : FPName} {A : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢ᵣ |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
  𝒢' ~ 𝒢ᵣ |ₕ [Γ‚ Δ] := by
  have ⟨hA, hB, rfl, hP⟩ := TypingStepₘ_inv_one_bot_source 𝒟 hStep
  exact hP
