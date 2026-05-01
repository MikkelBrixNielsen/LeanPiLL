import PiLL.Semantics.JudgementStep.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Parr_res

lemma TypingStepₘ_inv_parr_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {y y' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (y⸨y'⸩) 𝒟') :
  ∃ 𝒢ᵣ Γ A B,
    y ≠ y' ∧
    (𝒢 ~ 𝒢ᵣ |ₕ [y ∶ A ⅋ B :: Γ]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [y' ∶ A :: y ∶ B :: Γ]) := by
  generalize hl : (y⸨y'⸩ : Lbl) = l at hStep
  induction hStep <;> try simp only [HasBracket.brack, HasParen.paren, Lbl.act.injEq,
    reduceCtorEq, Act.parr.injEq] at hl
  case parr =>
    expose_names
    obtain ⟨h1, h2⟩ := hl
    subst h1 h2
    simp only [Finset.singleton_union, Finset.insert_union, Finset.mem_insert, Finset.mem_union,
      Env.mem_pair_fst_in_names_iff, not_or, ← ne_eq, not_exists] at hy
    refine ⟨∅, Γ, A, B, hy.1.symm, by simp, by simp⟩
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Γ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥 |ₕ ℋ, Γ, A, B, hxx',  ?_, ?_⟩
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact HyperEnv.Perm_exchange_rhs (HyperEnv.Perm.merge_comm) hP
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      exact hP'.trans HyperEnv.Perm.merge_comm
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Γ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒢_1 |ₕ 𝒥, Γ, A, B, hxx', ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hP'
  case res 𝒥 𝒥' Γ Γ' Δ Δ' Q Q' A m l' L L' huniq huniq' z w hzw
    hz_pre hw_pre hz_post hw_post hlz hlw _ ih =>
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒦, Ξ, C, D, hxx', hP, hP'⟩ := ih
    simp only [Lbl.f, fNamesAct, Lbl.i, iNamesAct, Finset.mem_union, not_or,
      Finset.notMem_singleton] at hlz hlw
    obtain ⟨hzx, hzx'⟩ := hlz
    obtain ⟨hyx, hyx'⟩ := hlw
    simp only [Finset.mem_union, not_or, and_assoc] at hz_pre hw_pre hz_post hw_post
    obtain ⟨𝒢ₙ, Γₙ, h_pre_res, h_post_res⟩ := HyperEnv.Perm.extract_parr_res
      hP hP' hxx' hzx hzx' hyx hyx' hz_pre.2.1 hw_pre.2.1 hz_post.2.1 hw_post.2.1
      hzw hz_pre.2.2.2 hw_pre.2.2.1
    refine ⟨𝒢ₙ, Γₙ, C, D, hxx', ?_, ?_⟩
    · exact h_pre_res
    · exact h_post_res
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Δ, A, B, hxx', ?_, hP'⟩
    exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasParen.paren, true_implies] at ih
    obtain ⟨𝒥, Δ, A, B, hxx', hP, hP'⟩ := ih
    refine ⟨𝒥, Δ, A, B, hxx', ?_, ?_⟩
    · exact hP1.symm.trans hP
    · exact hP2.symm.trans hP'
