import PiLL.Model.Judgement.Inversion.Lemmas
import PiLL.Semantics.JudgementStep.Inversion.One_Bot
import PiLL.Semantics.JudgementStep.Inversion.Res
import PiLL.Semantics.JudgementStep.Inversion.Tensor_parr
import PiLL.Semantics.JudgementStep.Properties.Linearity
import PiLL.Semantics.ProcStep.Basic

theorem typability_subject_reductionₘ
  {n : Nat} {𝒢 : HyperEnv} {P P' : Proc} {l : Lbl}
  (𝒟 : Typing n P 𝒢) (hPS : ProcStepₘ P l P') :
  ∃ (𝒢' : HyperEnv) (𝒟' : Typing n P' 𝒢'),
    TypingStepₘ 𝒟 l 𝒟' := by
  induction hPS generalizing n 𝒢
  case one =>
    obtain ⟨hP, 𝒟'⟩ := Typing_inv_one 𝒟
    have ⟨Δ, heq, hPΔ⟩:= HyperEnv.Perm_singleton_inv hP.symm
    simp only [HasPerm.perm, List.singleton_perm] at hPΔ
    subst hPΔ heq
    use ∅, 𝒟'
    apply TypingStepₘ.one
  case bot =>
    obtain ⟨Γ, hP, 𝒟'⟩ := Typing_inv_bot 𝒟
    have := HyperEnv.Nodup_perm hP (Typing_preserves_linearity 𝒟).1
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons] at this
    obtain ⟨hxΓ, _⟩ := this
    use [Γ], 𝒟'
    exact TypingStepₘ.perm_hyper (𝒟' := 𝒟') hP.symm (by rfl) (TypingStepₘ.bot (hF := hxΓ))
  case tensor Q x y hF =>
    obtain ⟨A, B, Γ, Δ, L, hP, 𝒟'⟩ := Typing_inv_tensor 𝒟
    simp only [Finset.singleton_union, Finset.mem_insert, not_or, ← ne_eq] at hF
    obtain ⟨hF1, hF2⟩ := hF
    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ Q.f)
    simp only [Finset.union_singleton, Finset.insert_union, Finset.mem_insert, Finset.mem_union,
      not_or, ← ne_eq] at hz
    obtain ⟨hzy, hz, hfz⟩ := hz
    have 𝒟z := (𝒟' z hz)
    have hfy := Proc.not_mem_f_open hzy hfz hF2
    rw [(Typing_f_eq_names 𝒟z)] at hfy
    have ⟨hyΓ, hyΔ⟩ : y ∉ Γ.names ∧ y ∉ Δ.names := by
      constructor <;> (intro hc ; simp [hc] at hfy)
    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names ∪ Δ.names := by simp [hF2, hyΓ, hyΔ, hF1]
    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons, Env.names_merge,
      Finset.mem_union, not_or] at hnd'
    have 𝒟y := Typing_tensor_all_fresh 𝒟' y hy
    · use [y ∶ A :: Γ] |ₕ [x ∶ B :: Δ], 𝒟y
      apply TypingStepₘ.perm_hyper hP.symm (by rfl)
      apply TypingStepₘ.tensor
      · exact hnd'.1
      · exact 𝒟'
      · exact hy
  case parr Q x y hF =>
    obtain ⟨A, B, Γ, L, hP, 𝒟'⟩ := Typing_inv_parr 𝒟
    simp only [Finset.singleton_union, Finset.mem_insert, not_or, ← ne_eq] at hF
    obtain ⟨hF1, hF2⟩ := hF
    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {y} ∪ Q.f)
    simp only [Finset.union_singleton, Finset.insert_union, Finset.mem_insert, Finset.mem_union,
      not_or, ← ne_eq] at hz
    obtain ⟨hzy, hz, hfz⟩ := hz
    have 𝒟z := (𝒟' z hz)
    have hfy := Proc.not_mem_f_open hzy hfz hF2
    rw [(Typing_f_eq_names 𝒟z)] at hfy
    have hyΓ : y ∉ Γ.names := by intro hc ; simp [hc] at hfy
    have hy : y ∉ {x} ∪ Q.f ∪ Γ.names := by simp [hF2, hyΓ, hF1]
    have ⟨hnd, hpw⟩ := Typing_preserves_linearity 𝒟
    have hnd' := HyperEnv.Nodup_perm hP hnd
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_cons] at hnd'
    have 𝒟y := Typing_parr_all_fresh 𝒟' y hy
    · use [y ∶ A :: x ∶ B :: Γ], 𝒟y
      apply TypingStepₘ.perm_hyper hP.symm (by rfl)
      apply TypingStepₘ.parr
      · exact hnd'.1
      · exact 𝒟'
      · exact hy
  case par₁ disj ih =>
    have ⟨𝒥, 𝒦, hP, hTQ, hTR, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTQ', hStepQQ'⟩ := ih hTQ
    have hD' : Disjoint 𝒥'.names 𝒦.names :=
      TypingStepₘ_par_preserves_disjoint hTR hStepQQ' hD disj
    use 𝒥' |ₕ 𝒦, (Typing.mix hD' hTQ' hTR)
    apply TypingStepₘ.perm_hyper hP.symm (by rfl)
    · apply TypingStepₘ.par₁ hStepQQ' disj
      · exact hD
      · exact hD'
      · exact hTR
  case par₂ disj ih =>
    have ⟨𝒦, 𝒥, hP, hTR, hTQ, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTQ', hStepQQ'⟩ := ih hTQ
    have hD' : Disjoint 𝒦.names 𝒥'.names :=
      (TypingStepₘ_par_preserves_disjoint hTR hStepQQ' hD.symm disj).symm
    use 𝒦 |ₕ 𝒥', (Typing.mix hD' hTR hTQ')
    apply TypingStepₘ.perm_hyper hP.symm (by rfl)
    · apply TypingStepₘ.par₂ hStepQQ' disj
      · exact hD
      · exact hD'
      · exact hTR
  case syn l' l'' _ _ disj lwf ih1 ih2 =>
    have ⟨𝒥, 𝒦, hP, hTR, hTQ, hD⟩ := Typing_inv_par 𝒟
    have ⟨𝒥', hTR', hStepRR'⟩ := ih1 hTR
    have ⟨𝒦', hTQ', hStepQQ'⟩ := ih2 hTQ
    have hD' : 𝒥'.disjoint 𝒦' :=
      TypingStepₘ_syn_preserves_disjoint hStepRR' hStepQQ' hD disj lwf
    use 𝒥' |ₕ 𝒦', (Typing.mix ?_ hTR' hTQ')
    · apply TypingStepₘ.perm_hyper hP.symm (by rfl)
      · apply TypingStepₘ.syn
        · exact hD
        · exact hD'
        · exact hStepRR'
        · exact hStepQQ'
        · exact disj
        · exact lwf
    · exact hD'
  case one_bot Q Q' x y hxQf hyQf hxy hPS ih =>
    have ⟨A, Γ, Δ, ℋ, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    have hNames := Typing_f_eq_names 𝒟
    simp only [Proc.f_cut, HyperEnv.names_eq_of_perm hP, HyperEnv.names_merge, HyperEnv.names_cons,
      Env.names_merge, HyperEnv.names_nil, Finset.union_empty] at hNames
    let hxQf' := hxQf
    let hyQf' := hyQf
    simp only [hNames, Finset.mem_union, not_or] at hxQf' hyQf'
    obtain ⟨hxℋ, hxΓ, hxΔ⟩ := hxQf'
    obtain ⟨hyℋ, hyΓ, hyΔ⟩ := hyQf'
    have hx_bound_t : x ∉ Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hxQf, hxℋ⟩, hxΓ⟩, hxΔ⟩
    have hy_bound_t : y ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hyQf, hyℋ⟩, hyΓ⟩, hyΔ⟩
    have hx_bound : x ∉ ({y} ∪ Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq]
      exact ⟨⟨⟨hxy, hxQf⟩, hxℋ⟩, hxΔ⟩
    have hy_bound : y ∉ (Q.f ∪ ℋ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨hyQf, hyℋ⟩, hyΔ⟩
    have 𝒟xy := (Typing_res_all_fresh 𝒟' x y hx_bound_t hy_bound_t hxy)
    have ⟨_, _, hTS_t⟩ := ih 𝒟xy
    have ⟨hA, hB, hΓ, _⟩ := TypingStepₘ_inv_one_bot_source 𝒟xy hTS_t
    subst hA hΓ
    rw! [hB] at *
    have := (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    obtain ⟨𝒢', 𝒟'', hTS'⟩ := ih (Typing_one_bot_all_fresh 𝒟' x y hx_bound hy_bound)
    have ⟨_, _, _, hP𝒢'⟩ := TypingStepₘ_inv_one_bot_source this hTS'
    refine ⟨𝒢', 𝒟'', ?_⟩
    apply TypingStepₘ.perm_hyper hP.symm hP𝒢'.symm
    · apply TypingStepₘ.one_bot (𝒢' := 𝒢') (huniq := 𝒟') (hx := hx_bound) (hy := hy_bound)
      · exact TypingStepₘ.perm_hyper (by rfl) hP𝒢' hTS'
  case tensor_parr Q Q' x x' y y' hxQf hyQf hx'Qf hy'Qf hxQ'f hyQ'f hx'Q'f hy'Q'f
    hxx' hxy hxy' hyx' hyy' hx'y' hPS ih =>
    generalize heq : (𝑣⸨•,•⸩ Q) = R at 𝒟
    induction 𝒟 generalizing Q <;> try contradiction
    case exchange_env hP ih' =>
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih' hxQf hyQf hx'Qf hy'Qf hPS ih heq
      expose_names
      refine ⟨𝒢_post, 𝒟_post, ?_⟩
      apply TypingStepₘ.perm_env hP hTS_post
    case exchange_hyper hP ih' =>
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih' hxQf hyQf hx'Qf hy'Qf hPS ih heq
      expose_names
      refine ⟨𝒢_post, 𝒟_post, ?_⟩
      apply TypingStepₘ.perm_hyper hP (by rfl) hTS_post
    case cut 𝒢 Γ Δ _ A m L 𝒟 ih' =>
      injection heq with hPQ
      subst hPQ
      have hNames := Typing_f_eq_names (Typing.cut L 𝒟)
      simp only [Proc.f_cut, HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge,
        HyperEnv.names_nil, Finset.union_empty] at hNames
      let hxQf_t := hxQf
      let hyQf_t := hyQf
      let hxQf_t' := hx'Qf
      let hyQf_t' := hy'Qf
      simp only [hNames, Finset.mem_union, not_or] at hxQf_t hyQf_t hxQf_t' hyQf_t'
      have hx_bound : x ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hxQf, hxQf_t⟩
      have hy_bound : y ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hyQf, hyQf_t⟩
      have hx'_bound : x' ∉ {y'} ∪ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, Finset.mem_singleton, not_or, ← ne_eq, and_assoc]
        exact ⟨hx'y', ⟨hx'Qf, hxQf_t'⟩⟩
      have hy'_bound : y' ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
        simp only [Finset.mem_union, not_or, and_assoc]
        exact ⟨hy'Qf, hyQf_t'⟩
      have 𝒟xy := Typing_res_all_fresh 𝒟 x y hx_bound hy_bound hxy
      obtain ⟨𝒢_post, 𝒟_post, hTS_post⟩ := ih 𝒟xy
      have ⟨C, D, E, F, Γ₁, Γ₂, hA, hA', hΓ, hP_post'⟩ :=
        TypingStepₘ_inv_tensor_parr_source 𝒟xy hTS_post
      subst hA
      let hA'_t := hA'
      simp only [Types.dual, Types.parr.injEq] at hA'_t
      obtain ⟨hA'_t1, hA'_t2⟩ := hA'_t
      subst hA'_t1 hA'_t2
      have 𝒟xy_rw : m ⊢ Q⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ C ⨂ D :: Γ] |ₕ [y ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        exact 𝒟xy
      have hP_pre_rw : ∀ z w,
        𝒢 |ₕ [z ∶ C ⨂ D :: Γ] |ₕ [w ∶ Cᗮ ⅋ Dᗮ :: Δ] ~
        𝒢 |ₕ [z ∶ C ⨂ D :: Γ₁‚ Γ₂] |ₕ [w ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        intros z w
        exact HyperEnv.Perm_merge_cancel_right_inv (HyperEnv.Perm.merge (by rfl)
          (HyperEnv.Perm_singleton_singleton.mpr (List.Perm.cons _ hΓ)))
      have step_rw : TypingStepₘ 𝒟xy_rw (x⟦x'⟧ |ₗ y⸨y'⸩) 𝒟_post := by
        apply TypingStepₘ.perm_hyper ?_ (by rfl) hTS_post
        rw [hA']
      have hTS_post' := TypingStepₘ.perm_hyper (hP_pre_rw x y) hP_post' step_rw
      have 𝒟_post' := Typing.exchange_hyper 𝒟_post hP_post'
      let L' := Q.f ∪ 𝒢.names ∪ (Γ₁‚ Γ₂).names ∪ Δ.names
      have huinq_pre : ∀ x ∉ L', ∀ y ∉ L', x ≠ y →
        m ⊢ Q⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ C ⨂ D :: Γ₁‚ Γ₂] |ₕ [y ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
        intros a ha b hb hab
        have hΓ_names : Γ.names = (Γ₁‚ Γ₂).names := Env.names_eq_of_perm hΓ
        have ha_bound : a ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
          simp only [L', hΓ_names, Finset.mem_union, not_or] at ⊢ ha
          exact ha
        have hb_bound : b ∉ Q.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names := by
          simp only [L', hΓ_names, Finset.mem_union, not_or] at ⊢ hb
          exact hb
        have 𝒟ab := Typing_res_all_fresh 𝒟 a b ha_bound hb_bound hab
        have 𝒟ab_rw : m ⊢ Q⸨#a, #b⸩ ∷ 𝒢 |ₕ [a ∶ C ⨂ D :: Γ] |ₕ [b ∶ Cᗮ ⅋ Dᗮ :: Δ] := by
          exact 𝒟ab
        exact Typing.exchange_hyper 𝒟ab (hP_pre_rw a b)
      have hL' : x ∉ L' ∧ y ∉ L' ∧ x' ∉ L' ∧ y' ∉ L' := by
        have hΓ_names : Γ.names = (Γ₁‚ Γ₂).names := Env.names_eq_of_perm hΓ
        simp only [L', ← hΓ_names, Finset.mem_union, not_or]
          at ⊢ hx_bound hy_bound hx'_bound hy'_bound
        exact ⟨⟨⟨⟨hxQf, hx_bound.1.1.2⟩, hx_bound.1.2⟩, hx_bound.2⟩,
               ⟨⟨⟨hyQf, hy_bound.1.1.2⟩, hy_bound.1.2⟩, hy_bound.2⟩,
               ⟨⟨⟨hx'Qf, hx'_bound.1.1.2⟩, hx'_bound.1.2⟩, hx'_bound.2⟩,
               ⟨⟨⟨hy'Qf, hy'_bound.1.1.2⟩, hy'_bound.1.2⟩, hy'_bound.2⟩⟩
      have huniq_post : ∀ z ∉ L', ∀ w ∉ L', z ≠ w → ∀ z' ∉ L',
        ∀ w' ∉ L', z' ≠ w' → z ≠ z' → z ≠ w' → w ≠ z' → w ≠ w' →
        m ⊢ Q'⸨2 | #z, #w⸩⸨#z', #w'⸩ ∷
          𝒢 |ₕ [z ∶ D :: Γ₂] |ₕ [z' ∶ C :: Γ₁] |ₕ [w' ∶ Cᗮ :: w ∶ Dᗮ :: Δ] := by
        intros z hzL w hwL hzw z' hz'L w' hw'L hz'w' hzz' hzw' hwz' hww'
        have hsubL' : 𝒢.names ∪ (Γ₂‚ Γ₁).names ∪ Δ.names ⊆ L' := by
          simp only [Env.names_merge, Finset.union_assoc, L']
          rw [← Finset.union_assoc Γ₂.names Γ₁.names _, Finset.union_comm _ Γ₁.names,
            Finset.union_assoc]
          exact Finset.subset_union_right
        exact Typing_tensor_parr_post_all_fresh L' 𝒟_post' hL'.1 hL'.2.1 hL'.2.2.1 hL'.2.2.2
          hsubL' hxQ'f hyQ'f hx'Q'f hy'Q'f hxx' hxy hxy' hyx' hyy' hx'y' z hzL w hwL
          hzw z' hz'L w' hw'L hz'w' hzz' hzw' hwz' hww'
      have hP_rw : 𝒢 |ₕ [(Γ₁‚ Γ₂)‚ Δ] ~  𝒢 |ₕ [Γ‚ Δ] := by
        apply HyperEnv.Perm.merge (by rfl)
        rw [HyperEnv.Perm_singleton_singleton]
        apply List.Perm.append hΓ.symm (by rfl)
      have hTS_raw := TypingStepₘ.tensor_parr
        (L := L') (huniq := huinq_pre) (huniq' := huniq_post)
        (hx := hL'.1) (hy := hL'.2.1) (hneq := hxy)
        (hx' := hL'.2.2.1) (hy' := hL'.2.2.2) (hneq' := hx'y')
        (hxx' := hxx') (hxy' := hxy') (hyx' := hyx') (hyy' := hyy')
        (hxP := hxQf) (hyP := hyQf) (hx'P := hx'Qf) (hy'P := hy'Qf)
        (hxP' := hxQ'f) (hyP' := hyQ'f) (hx'P' := hx'Q'f) (hy'P' := hy'Q'f)
        hTS_post'
      have hTS_final := TypingStepₘ.perm_hyper hP_rw HyperEnv.Perm_refl hTS_raw
      exact ⟨_, _, hTS_final⟩
  case res Q Q' l' x y hxy hFx hFy hlx hly hES ih =>
    have ⟨A, Γ, Δ, ℋ, L, hP, 𝒟'⟩ := Typing_inv_res 𝒟
    have hNames := Typing_f_eq_names 𝒟
    simp only [Proc.f_cut, HyperEnv.names_eq_of_perm hP, HyperEnv.names_merge, HyperEnv.names_cons,
      Env.names_merge, HyperEnv.names_nil, Finset.union_empty] at hNames
    let hFx' := hFx
    let hFy' := hFy
    let hlx' := hlx
    let hly' := hly
    rw [hNames] at hFx' hFy'
    simp only [Finset.mem_union, not_or, Finset.union_assoc] at hFx hFy hFx' hFy' hlx' hly'
    obtain ⟨hlxf, hlxi⟩ := hlx'
    obtain ⟨hlyf, hlyi⟩ := hly'
    obtain ⟨hxℋ, hxΓ, hxΔ, hxQ'f⟩ := hFx'
    obtain ⟨hyℋ, hyΓ, hyΔ, hyQ'f⟩ := hFy'
    have hx_bound : x ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hFx.1, hxℋ⟩, hxΓ⟩, hxΔ⟩
    have hy_bound : y ∉ (Q.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names) := by
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨⟨hFy.1, hyℋ⟩, hyΓ⟩, hyΔ⟩
    have 𝒟xy := (Typing_res_all_fresh 𝒟' x y hx_bound hy_bound hxy)
    have ⟨𝒢xy', 𝒟xy', hTS_xy⟩ := ih 𝒟xy



    -- FIXME: TypingStepₘ_inv_res_source has changed
    sorry
    -- have ⟨𝒢', Γ', Δ', hP'⟩ := TypingStepₘ_inv_res_source 𝒟xy hTS_xy hlx hly
    -- have 𝒟xy' : n ⊢ Q'⸨#x, #y⸩ ∷ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] :=
    --   Typing.exchange_hyper 𝒟xy' hP'
    -- let L' := Q'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names
    -- have ⟨⟨hx𝒢', hxΓ', hxΔ'⟩, ⟨hy𝒢', hyΓ', hyΔ'⟩⟩ := Typing_res_fresh 𝒟xy'
    -- have hxL' : x ∉ L' := by simp [L', hxQ'f, hx𝒢', hxΓ', hxΔ']
    -- have hyL' : y ∉ L' := by simp [L', hyQ'f, hy𝒢', hyΓ', hyΔ']
    -- have hEnv : 𝒢'.names ∪ Γ'.names ∪ Δ'.names ⊆ L' := by
    --   intro a ha
    --   simp only [L', Finset.mem_union] at ⊢ ha
    --   rcases ha with h1 | hΔ'
    --   · rcases h1 with h𝒢' | hΓ'
    --     · left ; left ; right ; exact h𝒢'
    --     · left ; right ; exact hΓ'
    --   · right ; exact hΔ'
    -- have 𝒟'_post_L' : ∀ z ∉ L', ∀ w ∉ L', z ≠ w →
    --   n ⊢ Q'⸨#z, #w⸩ ∷ 𝒢' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'] := by
    --   apply Typing_res_post_all_fresh L' 𝒟xy' hxL' hyL' hxQ'f hyQ'f hEnv hxy
    -- have hTS_xy' : TypingStepₘ 𝒟xy l' 𝒟xy' :=
    --   TypingStepₘ.perm_hyper (by rfl) hP' hTS_xy
    -- refine ⟨𝒢' |ₕ [Γ'‚ Δ'], Typing.cut L' 𝒟'_post_L', ?_⟩
    -- apply TypingStepₘ.perm_hyper hP.symm HyperEnv.Perm_refl
    -- exact TypingStepₘ.res (L := L) (L' := L') (huniq := 𝒟') (huniq' := 𝒟'_post_L')
    --   hxy hx_bound hy_bound hxL' hyL' hlx hly hTS_xy'
