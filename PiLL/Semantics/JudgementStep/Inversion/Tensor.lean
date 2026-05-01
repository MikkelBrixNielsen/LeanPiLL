import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Tensor_res

lemma TypingStepₘ_inv_tensor_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧) 𝒟') :
  ∃ 𝒢ᵣ Γ₁ Γ₂ C D,
    x ≠ x' ∧
    (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γ₁‚ Γ₂]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁]) := by
  generalize hl : (x⟦x'⟧ : Lbl) = l at hStep
  induction hStep <;> try simp only [HasBracket.brack, HasParen.paren, Lbl.act.injEq,
    reduceCtorEq, Act.tensor.injEq] at hl
  case tensor =>
    expose_names
    obtain ⟨h1, h2⟩ := hl
    subst h1 h2
    use ∅, Γ, Δ, A, B
    simp only [Finset.singleton_union, Finset.insert_union, Finset.union_assoc, Finset.mem_insert,
      Finset.mem_union, Env.mem_pair_fst_in_names_iff, not_or, ← ne_eq, not_exists] at hy
    refine ⟨hy.1.symm, by simp, ?_⟩
    rw [HyperEnv.merge_unitL]
    exact HyperEnv.Perm.trans HyperEnv.Perm.merge_comm (HyperEnv.Perm.refl _)
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥 |ₕ ℋ, Γ, Δ, A, B, hxx',  ?_, ?_⟩
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_exchange_rhs (HyperEnv.Perm.merge_comm) hP
    · apply HyperEnv.Perm_rotate_rhs_left
      rw [← HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_rotate_rhs_right hP'
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒢_1 |ₕ 𝒥, Γ, Δ, A, B, hxx', ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      rw [← HyperEnv.merge_assoc]
      exact hP'
  case res 𝒥 𝒥' Γ Γ' Δ Δ' Q Q' A m l' L L' huniq huniq' z w hzw
    hz_pre hw_pre hz_post hw_post hlz hlw _ ih =>
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒦, Γ₁, Γ₂, C, D, hxx', hP, hP'⟩ := ih
    simp only [Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.mem_union, not_or,
      Finset.notMem_singleton] at hlz hlw
    obtain ⟨hzx, hzx'⟩ := hlz
    obtain ⟨hyx, hyx'⟩ := hlw
    simp only [Finset.mem_union, not_or, and_assoc] at hz_pre hw_pre hz_post hw_post
    have hP'' : 𝒥' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'] ~
      𝒦 |ₕ [x' ∶ C :: Γ₁] |ₕ [x ∶ D :: Γ₂] := by
      have :  𝒦 |ₕ [x' ∶ C :: Γ₁] |ₕ [x ∶ D :: Γ₂] ~ 𝒦 |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁] := by
        simp only [HyperEnv.merge_assoc]
        exact HyperEnv.Perm.merge (by rfl) HyperEnv.Perm.merge_comm
      apply hP'.trans this.symm
    obtain ⟨𝒢ₙ, Γₙ, Δₙ, h_pre_res, h_post_res⟩ := HyperEnv.Perm.extract_tensor_res
      hP hP'' hxx' hzx hzx' hyx hyx' hz_pre.2.1 hw_pre.2.1 hz_post.2.1 hw_post.2.1
      hzw hz_pre.2.2.2 hw_pre.2.2.1
    refine ⟨𝒢ₙ, Γₙ, Δₙ, C, D, hxx', ?_, ?_⟩
    · exact h_pre_res
    · have : 𝒢ₙ |ₕ [x' ∶ C :: Γₙ] |ₕ [x ∶ D :: Δₙ] ~ 𝒢ₙ |ₕ [x ∶ D :: Δₙ] |ₕ [x' ∶ C :: Γₙ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        apply HyperEnv.Perm.merge_comm
      exact h_post_res.trans this
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ₁, Γ₂, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Γ₁, Γ₂, A, B, hxx', ?_, hP'⟩
    exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, true_implies] at ih
    obtain ⟨𝒥, Γ₁, Γ₂, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Γ₁, Γ₂, A, B, hxx', ?_, ?_⟩
    · exact hP1.symm.trans hP
    · exact hP2.symm.trans hP'
