import PiLL.Semantics.JudgementStep.Basic
import PiLL.Semantics.JudgementStep.Inversion.Tensor
import PiLL.Semantics.JudgementStep.Inversion.Parr
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Tensor_Parr_res
import PiLL.Model.HyperEnvironment.Lemmas.Extraction.Tensor_Parr_Res_Crosslinked

lemma TypingStepₘ_inv_tensor_parr_existential {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' y y' : FPName} {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
  (∃ 𝒢ᵣ Γᵣ Δᵣ Ξᵣ A B C D,
    (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ] |ₕ [y ∶ C ⅋ D :: Ξᵣ]) ∧
    (𝒢' ~ 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ] |ₕ [y' ∶ C :: y ∶ D :: Ξᵣ])) ∨
  (∃ 𝒢ᵣ Γᵣ Δᵣ Ξᵣ A B C D,
    (𝒢 ~ 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γᵣ‚ Δᵣ ++ y ∶ C ⅋ D :: Ξᵣ]) ∧
    ((𝒢' ~ 𝒢ᵣ |ₕ [x ∶ B :: Δᵣ] |ₕ [x' ∶ A :: Γᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]) ∨
     (𝒢' ~ 𝒢ᵣ |ₕ [x' ∶ A :: Γᵣ] |ₕ [x ∶ B :: Δᵣ ++ y' ∶ C :: y ∶ D :: Ξᵣ]))) := by
  generalize hl : (x⟦x'⟧ |ₗ y⸨y'⸩) = l at hStep
  induction hStep <;> try simp only [HasBracket.brack, HasParen.paren, reduceCtorEq,
    Lbl.par.injEq] at hl
  case par₁ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    rcases ih with ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ | ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩
    · left
      refine ⟨𝒢ₙ |ₕ ℋ, Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
      · apply HyperEnv.Perm_rotate_rhs_left
        rw [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_right_inv
        exact HyperEnv.Perm_rotate_rhs_right hP
      · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm_merge_cancel_right_inv
        apply HyperEnv.Perm_rotate_rhs_right
        rw [← HyperEnv.merge_assoc]
        exact hP'
    · right
      refine ⟨𝒢ₙ |ₕ ℋ, Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
      · have h1 : 𝒢_1 |ₕ ℋ ~ (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ ++ y ∶ C ⅋ D :: Ξₙ]) |ₕ ℋ :=
          HyperEnv.Perm.merge hP (by rfl)
        have h2 : (𝒢ₙ |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ ++ y ∶ C ⅋ D :: Ξₙ]) |ₕ ℋ ~
          (𝒢ₙ |ₕ ℋ) |ₕ [x ∶ A ⨂ B :: Γₙ‚ Δₙ ++ y ∶ C ⅋ D :: Ξₙ] := by
          apply HyperEnv.Perm_rotate_rhs_right
          apply HyperEnv.Perm_merge_cancel_right_inv
          exact HyperEnv.Perm.merge_comm
        exact h1.trans h2
      · rcases hP' with hP'1 | hP'2
        · left
          rw [HyperEnv.merge_assoc]
          apply HyperEnv.Perm_rotate_rhs_right
          apply HyperEnv.Perm_merge_cancel_right_inv
          apply HyperEnv.Perm_rotate_rhs_right
          exact hP'1
        · right
          rw [HyperEnv.merge_assoc]
          apply HyperEnv.Perm_rotate_rhs_right
          apply HyperEnv.Perm_merge_cancel_right_inv
          apply HyperEnv.Perm_rotate_rhs_right
          exact hP'2
  case par₂ ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    rcases ih with ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ | ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩
    · left
      refine ⟨𝒢_1 |ₕ 𝒢ₙ , Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
      · simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        rw [← HyperEnv.merge_assoc]
        exact hP
      · simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        simp only [← HyperEnv.merge_assoc]
        exact hP'
    · right
      refine ⟨𝒢_1 |ₕ 𝒢ₙ , Γₙ, Δₙ, Ξₙ, A, B, C, D,  ?_, ?_⟩
      · simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        exact hP
      · rcases hP' with hP'1 | hP'2
        · left
          simp only [HyperEnv.merge_assoc]
          apply HyperEnv.Perm_merge_cancel_left_inv
          simp only [← HyperEnv.merge_assoc]
          exact hP'1
        · right
          simp only [HyperEnv.merge_assoc]
          apply HyperEnv.Perm_merge_cancel_left_inv
          simp only [← HyperEnv.merge_assoc]
          exact hP'2
  case syn ih1 ih2 =>
    expose_names
    obtain ⟨hl1, hl2⟩ := hl
    subst hl1 hl2
    obtain ⟨𝒢ᵣ, Γ₁, Γ₂, A, B, hxx', hP_pre, hP_post⟩ := TypingStepₘ_inv_tensor_existential h₁
    obtain ⟨𝒢ᵣ', Δ, C, D, hyy', hP_pre', hP_post'⟩ := TypingStepₘ_inv_parr_existential h₂
    left
    refine ⟨(𝒢ᵣ |ₕ 𝒢ᵣ'), Γ₁, Γ₂, Δ, A, B, C, D, ?_, ?_⟩
    · have hP_merge := HyperEnv.Perm.merge hP_pre hP_pre'
      have hP_trans : 𝒢ᵣ |ₕ [x ∶ A ⨂ B :: Γ₁‚ Γ₂] |ₕ (𝒢ᵣ' |ₕ [y ∶ C ⅋ D :: Δ]) ~
        𝒢ᵣ |ₕ 𝒢ᵣ' |ₕ [x ∶ A ⨂ B :: Γ₁‚ Γ₂] |ₕ [y ∶ C ⅋ D :: Δ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        simp only [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_left
        simp only [HyperEnv.merge_assoc]
        exact HyperEnv.Perm_merge_cancel_left_inv HyperEnv.Perm.merge_comm
      exact hP_merge.trans hP_trans
    · have hP_merge' := HyperEnv.Perm.merge hP_post hP_post'
      have hP_trans' : 𝒢ᵣ |ₕ [x ∶ B :: Γ₂] |ₕ [x' ∶ A :: Γ₁] |ₕ (𝒢ᵣ' |ₕ [y' ∶ C :: y ∶ D :: Δ]) ~
        𝒢ᵣ |ₕ 𝒢ᵣ' |ₕ [x ∶ B :: Γ₂] |ₕ [x' ∶ A :: Γ₁] |ₕ [y' ∶ C :: y ∶ D :: Δ] := by
        simp only [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        conv_rhs => rw [← HyperEnv.merge_assoc]
        apply HyperEnv.Perm_rotate_rhs_left
        rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_merge_cancel_left_inv
        exact HyperEnv.Perm.merge_comm
      exact  hP_merge'.trans hP_trans'
  case res ih =>
    expose_names
    subst hl
    simp only [Lbl.f, fNamesAct, Finset.singleton_union, Lbl.i, iNamesAct, Finset.union_insert,
      Finset.insert_union, Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hlx hly
    simp only [Finset.union_assoc, Finset.mem_union, not_or] at hx_pre hy_pre hx_post hy_post
    rcases ih rfl with ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, A, B, C, D, hP_pre, hP_post⟩ |
      ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, A, B, C, D, hP_pre, hP_post_or⟩
    · rcases HyperEnv.Perm.extract_tensor_parr_res
          hP_pre hP_post
          hlx.2.1 hlx.1 hlx.2.2.1 hlx.2.2.2
          hly.2.1 hly.1 hly.2.2.1 hly.2.2.2
          hneq
          hx_pre.2.1 hy_pre.2.1 hx_post.2.1 hy_post.2.1
          hx_pre.2.2.2 hy_pre.2.2.1
      with ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, h_pre_res, h_post_res⟩ | ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, h_pre_res, h_post_res⟩
      · left
        refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, h_pre_res, h_post_res⟩
      · right
        refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, h_pre_res, h_post_res⟩
    · right
      obtain ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, h_pre_res, h_post_res⟩ :=
        HyperEnv.Perm.extract_tensor_parr_res_crosslinked
          hP_pre hP_post_or hlx.1 hlx.2.2.2 hly.1 hly.2.2.2 hlx.2.1
          hly.2.1 hly.2.2.1 hlx.2.2.1 hneq hx_pre.2.1 hx_post.2.1
          hy_pre.2.1 hy_post.2.1 hx_pre.2.2.1 hx_post.2.2.1 hx_pre.2.2.2
          hx_post.2.2.2 hy_pre.2.2.1 hy_post.2.2.1 hy_pre.2.2.2 hy_post.2.2.2
      refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, ?_⟩
      · exact h_pre_res
      · exact h_post_res
  case perm_env ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    rcases ih with ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ | ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'_or⟩
    · left
      refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, hP'⟩
      exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
    · right
      refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, hP'_or⟩
      exact (HyperEnv.Perm.cons (ℋ := 𝒢_1) hP1.symm (by rfl)).trans hP
  case perm_hyper ih =>
    expose_names
    subst hl
    simp only [HasBracket.brack, HasParen.paren, true_implies] at ih
    rcases ih with ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'⟩ | ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, hP, hP'_or⟩
    · left
      refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, ?_⟩
      · exact hP1.symm.trans hP
      · exact hP2.symm.trans hP'
    · right
      refine ⟨𝒢ₙ, Γₙ, Δₙ, Ξₙ, A, B, C, D, ?_, ?_⟩
      · exact hP1.symm.trans hP
      · rcases hP'_or with hP'_L | hP'_R
        · left ; exact hP2.symm.trans hP'_L
        · right ; exact hP2.symm.trans hP'_R

lemma TypingStepₘ_inv_tensor_parr_source {n n' : Nat} {P P' : Proc} {𝒢 𝒢' : HyperEnv}
  {x x' y y' : FPName} {A B : Types} {Γ Δ : Env} {𝒟' : n' ⊢ P' ∷ 𝒢'}
  (𝒟 : n ⊢ P ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ])
  (hStep : TypingStepₘ 𝒟 (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟') :
  ∃ (C D E F : Types) (Γ₁ Γ₂ : Env),
    A = C ⨂ D ∧
    B = E ⅋ F ∧
    Γ ~ Γ₁‚ Γ₂ ∧
    𝒢' ~ 𝒢 |ₕ [x ∶ D :: Γ₂] |ₕ [x' ∶ C :: Γ₁] |ₕ [y' ∶ E :: y ∶ F :: Δ] := by
  obtain h_left | h_right := TypingStepₘ_inv_tensor_parr_existential hStep
  · obtain ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, C, D, E, F, hP_pre, hP_post⟩ := h_left
    have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
    have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      HyperEnv.PairwiseDisjoint_merge, List.mem_cons, List.not_mem_nil, or_false,
      Env.names_distributes, Finset.singleton_union, Finset.disjoint_insert_right,
      Env.mem_pair_fst_in_names_iff, not_exists, forall_eq, forall_eq_or_imp] at hpw
    have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1
    have hxLHS : ∃ Γ', Γ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Γ' ~ x ∶ C ⨂ D :: Γᵣ‚ Δᵣ := by
      have hxRHS : (x ∶ C ⨂ D :: Γᵣ‚ Δᵣ) ∈
        𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] := by simp
      have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP_pre hxRHS
      simp only [HasPerm.perm] at hPΞ
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hΞ
      rcases hΞ with h1 | h2 | h3
      · exfalso
        exact (HyperEnv.not_mem_names_iff.mp hx𝒢 Ξ _ h1)
          ((List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ.symm).mp (by simp))
      · subst h2
        have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ).mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq, true_and] at hxin
        rcases hxin with ⟨rfl, _⟩ | h
        · refine ⟨(x ∶ C ⨂ D :: Γ), by simp, hPΞ⟩
        · exfalso ; exact hxΓ (Env.mem_pair_fst_in_names _ h)
      · subst h3
        have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΞ).mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at hxin
        rcases hxin with ⟨rfl, _⟩ | h
        · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
          Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
          not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
        · exfalso ; exact hxΔ (Env.mem_pair_fst_in_names _ h)
    have hyLHS : ∃ Δ', Δ' ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ B :: Δ] ∧ Δ' ~ y ∶ E ⅋ F :: Ξᵣ := by
      have hyRHS : (y ∶ E ⅋ F :: Ξᵣ) ∈ 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] := by simp
      have ⟨Ξ, hΞ, hPΞ⟩ := HyperEnv.Perm_mem hP_pre hyRHS
      simp only [HasPerm.perm] at hPΞ
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hΞ
      rcases hΞ with h1 | h2 | h3
      · exfalso
        exact (HyperEnv.not_mem_names_iff.mp hy𝒢 Ξ _ h1)
          ((List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ.symm).mp (by simp))
      · subst h2
        have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ).mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at hyin
        rcases hyin with ⟨rfl, _⟩ | h
        · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
          Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
          not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
        · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
      · subst h3
        have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΞ).mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq, true_and] at hyin
        rcases hyin with ⟨rfl, _⟩ | h
        · refine ⟨(y ∶ E ⅋ F :: Δ), by simp, hPΞ⟩
        · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ h)
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hxLHS hyLHS
    rcases hxLHS with ⟨Γ', hΓ', hPΓ'⟩
    rcases hyLHS with ⟨Δ', hΔ', hPΔ'⟩
    rcases hΓ' with h1 | h2 | h3
    · exfalso
      exact HyperEnv.not_mem_names_iff.mp
        hx𝒢 Γ' _ h1 ((List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ'.symm).mp (by simp))
    · subst h2
      rcases hΔ' with h4 | h5 | h6
      · exfalso
        exact HyperEnv.not_mem_names_iff.mp
          hy𝒢 Δ' _ h4 ((List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ'.symm).mp (by simp))
      · subst h5
        have hyin := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ').mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq] at hyin
        rcases hyin with ⟨rfl, _⟩ | h
        · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
          Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
          not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
        · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
      · subst h6
        have hx_eq := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ').mpr (by simp)
        simp only [List.mem_cons, Prod.mk.injEq, true_and] at hx_eq
        rcases hx_eq with ⟨rfl, hA_eq⟩ | hx_eq
        · have hy_eq := (List.Perm.mem_iff (a := y ∶ E ⅋ F) hPΔ').mpr (by simp)
          simp only [List.mem_cons, Prod.mk.injEq, true_and] at hy_eq
          rcases hy_eq with ⟨rfl, hB_eq⟩ | hy_eq
          · have hPΓ := List.Perm.cons_inv hPΓ'
            have hPΔ := List.Perm.cons_inv hPΔ'
            refine ⟨C, D, E, F, Γᵣ, Δᵣ, rfl, rfl, hPΓ, ?_⟩
            have hP1 : [x ∶ C ⨂ D :: Γ] ~ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΓ)
            have hP2 : [y ∶ E ⅋ F :: Δ] ~ [y ∶ E ⅋ F :: Ξᵣ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hPΔ)
            have hP3 : 𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γ] |ₕ [y ∶ E ⅋ F :: Δ] ~
              𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ‚ Δᵣ] |ₕ [y ∶ E ⅋ F :: Ξᵣ] :=
              HyperEnv.Perm.merge (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP1) hP2
            have hP4 := hP_pre.trans hP3.symm
            apply HyperEnv.Perm_merge_cancel_right at hP4
            apply HyperEnv.Perm_merge_cancel_right at hP4
            have hP5 := hP_post.trans (HyperEnv.Perm.merge
              (HyperEnv.Perm.merge (HyperEnv.Perm.merge hP4.symm
                (HyperEnv.Perm.refl _)) (HyperEnv.Perm.refl _)) (HyperEnv.Perm.refl _))
            have hP6 : [y' ∶ E :: y ∶ F :: Ξᵣ] ~ [y' ∶ E :: y ∶ F :: Δ] :=
              HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ (List.Perm.cons _ hPΔ.symm))
            exact hP5.trans (HyperEnv.Perm.merge (HyperEnv.Perm.refl _) hP6)
          · exfalso ; exact hyΔ (Env.mem_pair_fst_in_names _ hy_eq)
        · exfalso ; exact hxΓ (Env.mem_pair_fst_in_names _ hx_eq)
    · subst h3
      have hxin := (List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ').mpr (by simp)
      simp only [List.mem_cons] at hxin
      rcases hxin with ⟨rfl, _⟩ | h
      · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
        Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
        not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
      · exfalso ; exact hxΔ (Env.mem_pair_fst_in_names _ h)
  · obtain ⟨𝒢ᵣ, Γᵣ, Δᵣ, Ξᵣ, C, D, E, F, hP_pre, _⟩ := h_right
    have ⟨hdn, hpw⟩ := Typing_preserves_linearity 𝒟
    have ⟨⟨hx𝒢, hxΓ, hxΔ⟩, ⟨hy𝒢, hyΓ, hyΔ⟩⟩ := Typing_res_fresh 𝒟
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      HyperEnv.PairwiseDisjoint_merge, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      Env.names_distributes, Finset.singleton_union, Finset.disjoint_insert_right,
      Env.mem_pair_fst_in_names_iff, not_exists, forall_eq] at hpw
    have hDΓΔ := HyperEnv.PairwiseDisjoint_implies_disjoint hpw.2.1
    have hxRHS : (x ∶ C ⨂ D :: Γᵣ ++ Δᵣ ++ y ∶ E ⅋ F :: Ξᵣ) ∈
      𝒢ᵣ |ₕ [x ∶ C ⨂ D :: Γᵣ ++ Δᵣ ++ y ∶ E ⅋ F :: Ξᵣ] := by simp
    have ⟨Γ', hΓ', hPΓ'⟩:= HyperEnv.Perm_mem hP_pre hxRHS
    simp only [HasPerm.perm, List.cons_append, List.append_assoc] at hPΓ'
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hΓ'
    rcases hΓ' with h1 | h2 | h3
    · exfalso
      exact HyperEnv.not_mem_names_iff.mp hx𝒢 Γ' _ h1
        ((List.Perm.mem_iff (a := x ∶ C ⨂ D) hPΓ').mpr (by simp))
    · subst h2
      have hyin : (y, E ⅋ F) ∈ x ∶ C ⨂ D :: (Γᵣ ++ (Δᵣ ++ y ∶ E ⅋ F :: Ξᵣ)) := by simp
      have hyinΓ' := (List.Perm.mem_iff hPΓ'.symm).mp hyin
      simp only [List.mem_cons, Prod.mk.injEq] at hyinΓ'
      rcases hyinΓ' with ⟨rfl, _⟩ | h
      · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
        Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
        not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
      · exfalso ; exact hyΓ (Env.mem_pair_fst_in_names _ h)
    · subst h3
      have hxin : (x, C ⨂ D) ∈ x ∶ C ⨂ D :: (Γᵣ ++ (Δᵣ ++ y ∶ E ⅋ F :: Ξᵣ)) := by simp
      have hxinΔ' := (List.Perm.mem_iff hPΓ').mpr hxin
      simp only [List.mem_cons, Prod.mk.injEq] at hxinΔ'
      rcases hxinΔ' with ⟨rfl, _⟩ | h
      · simp only [Env.disjoint, Env.names_distributes, Finset.singleton_union,
        Finset.disjoint_insert_right, Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or,
        not_true_eq_false, Finset.disjoint_insert_left, not_exists, false_and] at hDΓΔ
      · exfalso ; exact hxΔ (Env.mem_pair_fst_in_names _ h)
