import PiLL.Framework.Model.Judgement

lemma Typing.f_subset_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
  P.f ⊆ 𝒢.names := by
  induction h

  case mix₀ =>
    simp only [Proc.f, HyperEnv.names_empty, subset_refl]

  case mix ihP ihQ =>
    simp
    exact Finset.union_subset_union ihP ihQ

  case one | bot | w =>
    simp only [Proc.f, HyperEnv.names_singleton,
      Env.names_distributes, Env.names_singleton]
    simp_all

  case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.insert_subset
    · simp
    · exact ih

  case amp ihP ihQ =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at *
    · apply Finset.insert_subset
      · simp
      · exact Finset.union_subset ihP ihQ

  case c ih =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.insert_subset
    · simp
    · intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
      specialize ih ha.1
      simp_all

  case ax =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton, Finset.union_singleton]
    simp [Finset.pair_comm]

  case cut ih =>
    simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    rw [Finset.mem_sdiff] at ha
    specialize ih ha.1
    simp_all

  case tensor ih | parr ih =>
    simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    simp at ⊢ ha ih
    rcases ha with rfl | ⟨hP, hny⟩
    · left ; rfl
    · specialize ih hP ; simp at ih ; tauto

theorem Typing.subst_name (𝒢 : HyperEnv) (P : Proc) (𝒟 : ⊢ P ∷ 𝒢) (x z : PName)
  (hFresh : x ∉ 𝒢.names) (hSafe : x ∉ P.boundNames) :
  ⊢ (P{x // z}) ∷ (𝒢{x // z}) := by
  induction 𝒟

  case mix₀ =>
    simp only [HyperEnv.substName_empty, Proc.substname_nil]
    apply Typing.mix₀

  case mix 𝒢' ℋ' _ _ hDisj 𝒟 ℰ ihP ihQ =>
    rw [HyperEnv.names_distributes, Finset.notMem_union] at hFresh
    simp only [← HyperEnv.substName_merge, ← Proc.substName_par]
    have this :  (𝒢'.substName x z).disjoint (ℋ'.substName x z) := by
      apply HyperEnv.substName_preserves_disjoint
      · apply hDisj
      · simp [HyperEnv.names] at ⊢ hFresh
        exact hFresh
    apply Typing.mix
    · exact this
    · apply ihP
      · exact hFresh.1
      · apply Proc.not_bound_par_left hSafe
        intro hxQf
        have hℋ' : x ∈ ℋ'.names := Typing.f_subset_names ℰ hxQf
        exact hFresh.2 hℋ'
    · apply ihQ
      · exact hFresh.2
      · apply Proc.not_bound_par_right hSafe
        intro hxPf
        have h𝒢' : x ∈ 𝒢'.names := Typing.f_subset_names 𝒟 hxPf
        exact hFresh.1 h𝒢'

  case ax =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton, Proc.substName_link]
    split
    · rename_i xp yp A hneq hxpz
      apply Typing.ax
      subst hxpz
      simp
      apply And.intro
      · exact hneq.symm
      · simp only [HyperEnv.names_singleton, Env.names_distributes,
          Env.names_singleton] at hFresh
        simp at hFresh
        exact hFresh.1
    · rename_i xp yp A hneq hxpnz
      apply Typing.ax
      simp only [HyperEnv.names_singleton, Env.names_distributes,
          Env.names_singleton] at hFresh
      split
      · simp at ⊢ hFresh
        intro h
        apply hFresh.right
        exact h.symm
      · exact hneq

  case one ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    split
    all_goals
      apply Typing.one
      simp at ih ; apply ih
      rw [HyperEnv.names_singleton, Env.names_singleton, Finset.mem_singleton] at hFresh
      simp [hFresh] at hSafe
      exact hSafe

  case bot ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    · apply Typing.bot
      all_goals (try
        rename_i hf _ hxpz
        subst hxpz
        rw [Env.substName_eq_self_of_not_mem]
        · exact hFresh.1
        · exact hf)
      · apply ih
        · exact hFresh.1
        · exact hSafe
    · apply Typing.bot
      all_goals (try
        rename_i hf _ _
        exact Env.not_mem_substName_intro hf hFresh.2.symm)
      · apply ih
        · exact hFresh.1
        · exact hSafe

  case oplus₁ ih | oplus₂ ih | quest ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    all_goals
    · constructor
      · simp_all
        exact ih

  case amp ihP ihQ =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ihP ihQ
    simp [hFresh] at hSafe
    rename_i Γ P' Q' xp A B D E
    have hsubP := Typing.f_subset_names D
    have hsubQ := Typing.f_subset_names E
    simp only [HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at hsubP hsubQ
    have this : x ∉ P'.boundNames ∧ x ∉ Q'.boundNames := by grind
    specialize ihP hFresh this.1
    specialize ihQ hFresh this.2
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton] at ihP ihQ
    split
    · apply Typing.amp <;> simp_all
      · exact ihP
      · exact ihQ
    · apply Typing.amp <;> simp_all
      · exact ihP
      · exact ihQ

  case bang h ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    all_goals
    · apply Typing.bang
      · simp_all
        exact ih
      · apply Env.serverUsable_substName
        exact h

  case w ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    · apply Typing.w
      · rename_i hf _ h
        rw [Env.substName_eq_self_of_not_mem]
        · exact hFresh.1
        · subst h
          exact hf
      · exact ih hFresh.1 hSafe
    · apply Typing.w
      · rename_i hf _ h
        exact Env.not_mem_substName_intro hf hFresh.2.symm
      · exact ih hFresh.1 hSafe

  case c Γ P' xp yp A hneq hf D ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh, ← ne_eq] at hSafe
    split_ifs
    · simp_all
    · apply Typing.c
      · exact hSafe.1
      · apply And.intro
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.1
          · rename_i h1 h2
            subst h1
            exact hf.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2
          · rename_i h1 h2
            subst h1
            exact hf.1
      · rw [Env.substName_eq_self_of_not_mem]
        · rename_i h1 h2
          specialize ih ⟨hFresh, hSafe.1⟩ hSafe.2
          simp only [HyperEnv.substName_singleton, Env.substName_distributes,
            Env.substName_singleton, h1, h2, if_true, if_false] at ih
          rw [Env.substName_eq_self_of_not_mem] at ih
          · exact ih
          · subst h1
            exact hf.1
        · rename_i h1 h2
          subst h1
          exact hf.1
    · apply Typing.c
      · exact hneq
      · apply And.intro
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.1
          · rename_i h1 h2
            subst h2
            exact hf.2
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2
          · rename_i h1 h2
            subst h2
            exact hf.2
      · rename_i h1 h2
        rw [Env.substName_eq_self_of_not_mem]
        · exact D
        · subst h2
          exact hf.2
    · apply Typing.c
      · exact hneq
      · apply And.intro
        · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
        · exact Env.not_mem_substName_intro hf.2 hSafe.1.symm
      · rename_i h1 h2
        specialize ih ⟨hFresh, hSafe.1⟩ hSafe.2
        simp [h1, h2]at ih
        exact ih

  case exists_ Γ P' xp A B X D ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    · apply Typing.exists_
      rename_i h
      subst h
      simp at ⊢ ih hFresh
      apply ih hFresh.1 hFresh.2
      exact hSafe
    · apply Typing.exists_
      rename_i h
      specialize ih hFresh hSafe
      simp [h] at ih
      exact ih

  case forall_ h ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
    simp [hFresh] at hSafe
    split
    all_goals
    · apply Typing.forall_
      · simp_all
        apply ih
      · rw [Env.ft_substName_eq_self]
        exact h

  case tensor hf hneq hDisj h ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh
    simp [hFresh, ← ne_eq] at hSafe
    split_ifs with h1 h2 h3
    · rw [h1, h2] at hneq
      contradiction
    · apply Typing.tensor
      · apply And.intro
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.1.1
          · subst h1 ; exact hf.1
        · apply And.intro
          · rw [Env.substName_eq_self_of_not_mem]
            · exact hFresh.1.2
            · subst h1 ; exact hf.2.1
          · apply And.intro
            · rw [Env.substName_eq_self_of_not_mem]
              · exact hf.2.2.1
              · subst h1 ; exact hf.1
            · rw [Env.substName_eq_self_of_not_mem]
              · exact hf.2.2.2
              · subst h1 ; exact hf.2.1
      · exact hSafe.1
      · apply Env.substName_preserves_disjoint
        · exact hDisj
        · exact hFresh.1
      · simp only [← HyperEnv.substName_merge, HyperEnv.substName_singleton,
          Env.substName_distributes, Env.substName_singleton, h1, h2, if_false,
          if_true] at ih
        apply ih
        · simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
            Env.names_distributes, Env.names_singleton, Finset.notMem_union,
            Finset.mem_singleton, ← ne_eq]
          apply And.intro
          · exact And.intro hFresh.1.1 hSafe.1
          · exact And.intro hFresh.1.2 (by subst h1 ; exact hFresh.2)
        · exact hSafe.2
    · apply Typing.tensor
      · apply And.intro
        · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
        · apply And.intro
          · rw [Env.substName_eq_self_of_not_mem]
            · exact hf.2.1
            · subst h3 ; exact hf.2.2.2
          · apply And.intro
            · rw [Env.substName_eq_self_of_not_mem]
              · exact hf.2.2.1
              · subst h3 ; exact hf.2.2.1
            · rw [Env.substName_eq_self_of_not_mem]
              · exact hf.2.2.2
              · subst h3 ; exact hf.2.2.2
      · exact hneq
      · apply Env.substName_preserves_disjoint
        · exact hDisj
        · exact hFresh.1
      · repeat rw [Env.substName_eq_self_of_not_mem]
        · exact h
        · subst h3 ; exact hf.2.2.2
        · subst h3 ; exact hf.2.2.1
    · apply Typing.tensor
      · apply And.intro
        · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
        · apply And.intro
          · exact Env.not_mem_substName_intro hf.2.1 hFresh.2.symm
          · apply And.intro
            · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.1.symm
            · exact Env.not_mem_substName_intro hf.2.2.2 hSafe.1.symm
      · exact hneq
      · apply Env.substName_preserves_disjoint
        · exact hDisj
        · exact hFresh.1
      · simp only [← HyperEnv.substName_merge, HyperEnv.substName_singleton,
          Env.substName_distributes, Env.substName_singleton, h1, h3, if_false] at ih
        apply ih
        · simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
            Env.names_distributes, Env.names_singleton, Finset.notMem_union,
            Finset.mem_singleton, ← ne_eq]
          apply And.intro
          · exact ⟨hFresh.1.1, hSafe.1⟩
          · exact ⟨hFresh.1.2, hFresh.2⟩
        · exact hSafe.2

  case parr hf hneq h ih =>
    simp only [HyperEnv.substName_singleton, Env.substName_distributes,
      Env.substName_singleton]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh
    simp [hFresh, ← ne_eq] at hSafe
    split_ifs with h1 h2 h3
    · apply Typing.parr
      · apply And.intro
        · rw [h1, h2] at hneq
          contradiction
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2
          · subst h2 ; exact hf.2
      · exact hSafe.1
      · rw [h1, h2] at hneq
        contradiction
    · apply Typing.parr
      · apply And.intro
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.1
          · subst h1 ; exact hf.1
        · apply Env.not_mem_substName_intro hf.2 hSafe.1.symm
      · exact hSafe.1
      · simp only [HyperEnv.substName_singleton, Env.substName_distributes,
          Env.substName_singleton, h1, h2, if_true, if_false] at ih
        apply ih
        · simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
            Finset.notMem_union, Finset.mem_singleton]
          exact ⟨⟨hFresh.1, hSafe.1,⟩, (by subst h1 ; exact hFresh.2)⟩
        · exact hSafe.2
    · apply Typing.parr
      · apply And.intro
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.1
          · subst h3 ; exact hf.2
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2
          · subst h3 ; exact hf.2
      · exact hneq
      · rw [Env.substName_eq_self_of_not_mem]
        · exact h
        · subst h3 ; exact hf.2
    · apply Typing.parr
      · apply And.intro
        · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
        · exact Env.not_mem_substName_intro hf.2 hSafe.1.symm
      · exact hneq
      · simp only [HyperEnv.substName_singleton, Env.substName_distributes,
          Env.substName_singleton, h1, h3, if_false] at ih
        apply ih
        · simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
            Finset.notMem_union, Finset.mem_singleton, ← ne_eq]
          exact ⟨⟨hFresh.1, hSafe.1⟩, hFresh.2⟩
        · exact hSafe.2

  case cut 𝒢' Γ' Δ' P' xp yp A hf hneq hDisj h ih =>
    simp only [HyperEnv.substName_distributes, HyperEnv.substName_singleton,
      Env.substName_distributes]
    conv_rhs => simp [HasSubst.subst, Proc.substName]
    simp only [HyperEnv.names_distributes, HyperEnv.names_singleton, Env.names_distributes,
      Finset.notMem_union] at hFresh
    simp [← ne_eq] at hSafe
    simp only [HyperEnv.substName_distributes, HyperEnv.substName_singleton,
      Env.substName_distributes, Env.substName_singleton, HyperEnv.names_distributes,
      HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
      Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at ih
    split_ifs with h1 h2 h3 h4
    · apply Typing.cut
      · split_ands
        · exact HyperEnv.not_mem_substName_intro hf.1 hSafe.2.1
        · exact Env.not_mem_substName_intro hf.2.1  hSafe.2.1.symm
        · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.2.1.symm
        · exact HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
        · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
        · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
      · exact hneq
      · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
      · rcases h1 with rfl | rfl
        all_goals
        · rw [HyperEnv.substName_eq_self_of_not_mem]
          · rw [Env.substName_eq_self_of_not_mem]
            · rw [Env.substName_eq_self_of_not_mem]
              · exact h
              · try exact hf.2.2.1
                try exact hf.2.2.2.2.2
            · try exact hf.2.1
              try exact hf.2.2.2.2.1
          · try exact hf.1
            try exact hf.2.2.2.1
    · simp [← ne_eq] at h1
      subst h2 h3
      contradiction
    · apply Typing.cut
      · split_ands
        · rw [HyperEnv.substName_eq_self_of_not_mem]
          · exact hFresh.1
          · subst h2 ; exact hf.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.2.1
          · subst h2 ; exact hf.2.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.2.2
          · subst h2 ; exact hf.2.2.1
        · exact HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
        · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
        · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
      · exact hSafe.1
      · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
      · simp only [h2, h3, if_true, if_false] at ih
        apply ih
        · subst h2
          exact ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩
        · exact hSafe.2.2

    · apply Typing.cut
      · split_ands
        · rw [HyperEnv.substName_eq_self_of_not_mem]
          · exact hf.1
          · subst h4 ; exact hf.2.2.2.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2.1
          · subst h4 ; exact hf.2.2.2.2.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hf.2.2.1
          · subst h4 ; exact hf.2.2.2.2.2
        · rw [HyperEnv.substName_eq_self_of_not_mem]
          · exact hFresh.1
          · subst h4 ; exact hf.2.2.2.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.2.1
          · subst h4 ; exact hf.2.2.2.2.1
        · rw [Env.substName_eq_self_of_not_mem]
          · exact hFresh.2.2
          · subst h4 ; exact hf.2.2.2.2.2
      · exact hSafe.2.1.symm
      · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
      · simp only [h2, h4, if_true, if_false] at ih
        apply ih
        · subst h4
          exact ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩
        · exact hSafe.2.2
    · apply Typing.cut
      · split_ands
        · exact HyperEnv.not_mem_substName_intro hf.1 hSafe.2.1
        · exact  Env.not_mem_substName_intro hf.2.1 hSafe.2.1.symm
        · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.2.1.symm
        · apply HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
        · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
        · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
      · exact hneq
      · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
      · simp only [h2, h4, if_false] at ih
        apply ih ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩ hSafe.2.2


lemma Types.subst_eq_self {T A : Types} {X : TVar} {hft : X ∉ T.freeTypes} :
  T.subst A X = T := by
  induction T <;> simp_all [Types.subst, Types.freeTypes, ← ne_eq]

  case var | varDual=>
    intro h
    subst h
    contradiction

  case forall_ ih | exist_ ih =>
    split_ifs with h
    · subst h ; rfl
    · simp_all only [forall_.injEq, exist_.injEq, true_and, ← ne_eq]
      apply ih
      intro h_contra
      simp [h_contra] at hft
      subst hft
      contradiction

lemma Types.freeTypes_dual_eq (T : Types) : T.dual.freeTypes = T.freeTypes := by
  induction T <;> simp_all [Types.freeTypes, Types.dual]

@[simp] lemma Types.not_mem_ft_subst {T A : Types} {X Y : TVar}
  (hT : Y ∉ T.freeTypes) (hA : Y ∉ A.freeTypes) (hneq : Y ≠ X) :
  Y ∉ (T.subst A X).freeTypes := by
  induction T <;> simp_all [Types.subst, Types.freeTypes, ← ne_eq]

  case var =>
    split_ifs with h
    · exact hA
    · simp [Types.freeTypes] ; exact hT

  case varDual =>
    split_ifs with h
    · simp [Types.freeTypes_dual_eq] ; exact hA
    · simp [Types.freeTypes] ; exact hT

  case forall_ A' ih | exist_ A' ih =>
    split_ifs with h1
    · simp [Types.freeTypes]
      intro hin
      have heq : Y = X := by
        rw [← h1]
        apply hT hin
      contradiction
    · simp only [Types.freeTypes, Finset.mem_sdiff, Finset.mem_singleton]
      intro h2
      have hog : Y ∈ A'.freeTypes := by
        by_contra hc
        apply ih at hc
        exact hc h2.1
      apply hT at hog
      exact h2.2 hog

lemma Types.subst_subst (T A B : Types) (X : TVar) :
  (T.subst A X).subst B X = T.subst (A.subst B X) X := by
  induction T generalizing A B <;> simp_all [Types.subst]

  case var | varDual =>
    split_ifs with h
    · (try erw [← Types.subst_dual]) ; rfl
    · simp [Types.subst]
      intro a
      contradiction

  case forall_ ih | exist_ ih =>
    split_ifs with h
    · simp [Types.subst]
    · simp [Types.subst]
      simp [h]
      apply ih

@[simp] lemma Types.subst_eq_self_of_not_mem (T A : Types) (X : TVar)
  (h : X ∉ T.freeTypes) : T.subst A X = T := by
  induction T <;> simp_all [Types.subst, Types.freeTypes]
  case var | varDual =>
    intro h
    subst h
    contradiction

  case forall_ ih | exist_ ih =>
    split_ifs with h1
    · subst h1 ; rfl
    · congr
      apply ih
      intro hin
      apply h at hin
      rw [hin] at h1
      contradiction

lemma Types.subst_commute (T A B : Types) (X Y : TVar) (hne : Y ≠ X) (hft : Y ∉ A.freeTypes) :
  (T.subst B Y).subst A X = (T.subst A X).subst (B.subst A X) Y := by
  induction T generalizing A B X Y <;> simp_all [Types.subst]

  case var =>
    split_ifs with h1 h2 h3 <;> simp_all [Types.subst]

  case varDual =>
    split_ifs with h1 h2 h3
    · simp_all
    · simp_all [Types.subst]
      erw [← Types.subst_dual]
      rfl
    · simp_all [Types.subst]
      symm
      apply Types.subst_eq_self_of_not_mem
      simp [Types.freeTypes_dual_eq, hft]
    · simp_all [Types.subst]

  case forall_ ih =>
    split_ifs with h1 h2 h3 <;> simp_all [Types.subst]
    sorry -- FIXME: Currently assuming Barendregt (add frehsness contraint?)

  case exist_ =>
    split_ifs with h1 h2 h3 <;> try simp_all [Types.subst]
    sorry -- FIXME: Currently assuming Barendregt (add frehsness contraint?)







@[simp] lemma Proc.substTypes_nil {A : Types} {X : TVar} : 𝟘{A // X} = 𝟘 := by rfl

@[simp] lemma Proc.substTypes_link {x y : PName} {A : Types} {X : TVar} :
  (x⟷ₚy){A // X} = x⟷ₚy := by rfl

@[simp] lemma Proc.substTypes_par {P Q : Proc} {A : Types} {X : TVar} :
  (P |ₚ Q){A // X} = P{A // X} |ₚ Q{A // X} := by rfl

@[simp] lemma Proc.substTypes_one {x : PName} {P : Proc} {A : Types} {X : TVar} :
  (x⟦⟧․P){A // X} = x⟦⟧․(P{A // X}) := by rfl

@[simp] lemma Proc.substTypes_bot {x : PName} {P : Proc} {A : Types} {X : TVar} :
  (x⸨⸩․P){A // X} = x⸨⸩․(P{A // X}) := by rfl

@[simp] lemma Proc.substTypes_output {x : PName} {P : Proc} {T A : Types} {X : TVar} :
  (x⟦T⟧․P){A // X} = x⟦T{A // X}⟧․(P{A // X}) := by rfl


@[simp] lemma Proc.substTypes_input_match {x : PName} {P : Proc} {A : Types} {X : TVar} :
  (x⸨X⸩․P){A // X} = x⸨X⸩․P := by
  simp [HasSubst.subst, Proc.substTypes, HasParen.paren]

@[simp] lemma Proc.substTypes_input_diff {x : PName} {P : Proc} {A : Types} {X Y : TVar}
  (hneq : Y ≠ X) : (x⸨Y⸩․P){A // X} = x⸨Y⸩․P{A // X} := by
  simp_all [HasSubst.subst, Proc.substTypes, HasParen.paren]





@[simp] lemma Env.substTypes_empty {A : Types} {X : TVar} :
  (∅ : Env){A // X} = (∅ : Env) := by rfl

@[simp] lemma Env.substTypes_singleton {x : PName} {T A : Types} {X : TVar} :
  (x ∶ T){A // X} = x ∶ T{A// X} := by
  simp only [HasSubst.subst, Env.substTypes, Env.mk, Finset.image_singleton]

@[simp] lemma Env.substTypes_distributes {Γ Δ : Env} {A : Types} {X : TVar} :
  (Γ‚ Δ){A // X} = Γ{A // X}‚ Δ{A // X} := by
  simp only [HasSubst.subst, Env.substTypes, Env.merge, Finset.image_union]

@[simp]
lemma Env.names_substTypes {Γ : Env} {A : Types} {X : TVar} :
  (Γ{A // X}).names = Γ.names := by
  simp only [Env.names, Env.substTypes, HasSubst.subst, Finset.image_image]
  apply Finset.image_congr
  intro ⟨n, T⟩ _
  rfl

@[simp] lemma Env.substTypes_preserves_disjoint {Γ Δ : Env} {A : Types} {X : TVar} :
  Γ{A // X}.disjoint Δ{A // X} = Γ.disjoint Δ := by
  simp only [Env.disjoint, Env.names_substTypes]

@[simp] lemma Env.substTypes_eq_self_of_not_mem {Γ : Env} {A : Types} {X : TVar}
  (h : X ∉ ft(Γ)ₑ) : Γ{A // X} = Γ := by
  simp only [HasSubst.subst, Env.substTypes]
  conv_rhs => rw [← Finset.image_id (s := Γ)]
  apply Finset.image_congr
  intro ⟨n, T⟩ hin
  simp
  apply Types.subst_eq_self
  simp only [Env.freeTypes, Finset.mem_biUnion, not_exists, not_and] at h
  exact h (n, T) hin

@[simp] lemma Env.not_mem_ft_substTypes {Γ : Env} {A : Types} {X Y : TVar} {hΓ : Y ∉ ft(Γ)ₑ}
  {hA : Y ∉ A.freeTypes} {hneq : Y ≠ X} : Y ∉ ft(Γ{A // X})ₑ := by
  simp only [HasSubst.subst, Env.substTypes, Env.freeTypes, Finset.mem_biUnion,
    not_exists, not_and]
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨op, hom, heq⟩
  subst heq
  apply Types.not_mem_ft_subst
  · rw [Env.freeTypes] at hΓ
    simp only [Finset.mem_biUnion, not_exists, not_and] at hΓ
    exact hΓ op hom
  · exact hA
  · exact hneq




@[simp] lemma Env.substTypes_mk {x : PName} {T A : Types} {X : TVar} :
  (x ∶ T){A // X} = x ∶ T.subst A X := by
  simp only [HasSubst.subst, Env.substTypes, Env.mk, Finset.image_singleton]

@[simp] lemma Env.freeTypes_empty :
  ft(∅)ₑ = ∅ := by simp only [Env.freeTypes, Finset.biUnion_empty]

@[simp] lemma Env.freeTypes_singleton {x : PName} {A : Types} :
  ft((x ∶ A : Env))ₑ = A.freeTypes := by
  simp only [Env.freeTypes, Env.freeTypes, Env.mk, Finset.singleton_biUnion]

@[simp] lemma Env.freeTypes_distributes {Γ Δ : Env} :
   (ft(Γ‚ Δ)ₑ) = (ft(Γ)ₑ ∪ ft(Δ)ₑ) := by
   simp only [Env.merge, Env.freeTypes, Finset.biUnion_union]

@[simp] lemma Env.freeTypes_notMem_merge {Γ Δ : Env} {X : TVar} :
   (X ∉ ft(Γ‚ Δ)ₑ) = (X ∉ ft(Γ)ₑ ∧ X ∉ ft(Δ)ₑ) := by
   simp only [Env.freeTypes_distributes, Finset.notMem_union]







@[simp] lemma HyperEnv.substTypes_empty {A : Types} {X : TVar} :
  (∅ : HyperEnv){A // X} = (∅ : HyperEnv) := by rfl

@[simp] lemma HyperEnv.substTypes_singleton {Γ : Env} {A : Types} {X : TVar} :
  ({Γ} : HyperEnv){A // X} = Γ{A // X} := by
  simp only [HasSubst.subst, HyperEnv.substTypes, Finset.image_singleton]

@[simp] lemma HyperEnv.substTypes_distributes {𝒢 ℋ : HyperEnv} {A : Types} {X : TVar} :
  (𝒢 |ₕ ℋ){A // X} = 𝒢{A // X} |ₕ ℋ{A // X} := by
  simp only [HasSubst.subst, HyperEnv.substTypes, HyperEnv.merge, Finset.image_union]

@[simp]
lemma HyperEnv.names_substTypes {𝒢 : HyperEnv} {A : Types} {X : TVar} :
  (𝒢{A // X}).names = 𝒢.names := by
  simp only [HyperEnv.names, HyperEnv.substTypes, HasSubst.subst]
  rw [Finset.image_biUnion]
  exact Finset.biUnion_congr rfl (by intro Γ _ ; apply Env.names_substTypes)

@[simp] lemma HyperEnv.substTypes_preserves_disjoint {𝒢 ℋ : HyperEnv} {A : Types} {X : TVar} :
  𝒢{A // X}.disjoint ℋ{A // X} = 𝒢.disjoint ℋ := by
  simp only [HyperEnv.disjoint, HyperEnv.names_substTypes]

@[simp] lemma HyperEnv.freeTypes_empty :
  ft(∅)ₕ = ∅ := by simp only [HyperEnv.freeTypes, Finset.biUnion_empty]

@[simp] lemma HyperEnv.freeTypes_singleton {Γ : Env} :
  ft(({Γ} : HyperEnv))ₕ = ft(Γ)ₑ := by
  simp only [HyperEnv.freeTypes, HyperEnv.freeTypes, Finset.singleton_biUnion]

@[simp] lemma HyperEnv.freeTypes_distributes {𝒢 ℋ : HyperEnv} :
   (ft(𝒢 |ₕ ℋ)ₕ) = (ft(𝒢)ₕ ∪ ft(ℋ)ₕ) := by
   simp only [HyperEnv.merge, HyperEnv.freeTypes, Finset.biUnion_union]

@[simp] lemma HyperEnv.freeTypes_notMem_merge {𝒢 ℋ : HyperEnv} {X : TVar} :
   (X ∉ ft(𝒢 |ₕ ℋ)ₕ) = (X ∉ ft(𝒢)ₕ ∧ X ∉ ft(ℋ)ₕ) := by
   simp only [HyperEnv.freeTypes_distributes, Finset.notMem_union]


attribute [simp] Types.freeTypes


theorem Typing.subst_types {𝒢 : HyperEnv} {P : Proc} {𝒟 : ⊢ P ∷ 𝒢}
  {A : Types} {X : TVar} : ⊢ (P{A // X}) ∷ (𝒢{A // X}) := by
  induction 𝒟 <;> simp [-Finset.singleton_union, -Finset.union_singleton] at *

  case mix₀ => apply Typing.mix₀

  case ax hneq =>
    apply Typing.ax
    exact hneq

  case mix hDisj _ _ ihP ihQ =>
    apply Typing.mix
    · simp [HyperEnv.substTypes_preserves_disjoint]
      exact hDisj
    · exact ihP
    · exact ihQ

  case one ih =>
    apply Typing.one
    · exact ih

  case bot hf _ ih =>
    apply Typing.bot
    · simp ; exact hf
    · apply ih

  case oplus₁ ih =>
    apply Typing.oplus₁
    exact ih

  case oplus₂ ih =>
    apply Typing.oplus₂
    exact ih

  case quest ih =>
    apply Typing.quest
    exact ih

  case amp ihP ihQ =>
    constructor
    · exact ihP
    · exact ihQ

  case c hneq hf _ ih =>
    apply Typing.c
    · exact hneq
    · simp ; exact hf
    · exact ih

  case w hf _ ih =>
    apply Typing.w
    · simp ; exact hf
    · apply ih

  case bang hsu ih =>
    all_goals
      apply Typing.bang
      · exact ih
      · apply Env.serverUsable_substTypes
        exact hsu

  case exists_ ih =>
    simp [HasSubst.subst, Types.subst] at ⊢ ih
    split_ifs with h
    · apply Typing.exists_
      simp_all only [HasSubst.subst, Types.subst_subst]
    · apply Typing.exists_
      rw [Types.subst_commute] at ih
      · exact ih
      · exact h
      · sorry -- FIXME: Currently assuming Barendregt (add freshness condition?)



  case forall_ D ft ih =>
    conv_lhs => rhs ; rhs ; simp [HasSubst.subst, Types.subst]
    split_ifs with h
    · subst h
      rw [Proc.substTypes_input_match]
      apply Typing.forall_
      · rw [Env.substTypes_eq_self_of_not_mem]
        · exact D
        · exact ft
      · rw [Env.substTypes_eq_self_of_not_mem]
        · exact ft
        · exact ft
    · rw [Proc.substTypes_input_diff]
      · apply Typing.forall_
        · apply ih
        · apply Env.not_mem_ft_substTypes
          · exact ft
          · sorry -- FIXME: Currently assuming Barendregt (could also add h : A.freeTypes = ∅)
          · exact h
      · exact h

  case tensor hf hneq hDisj _ ih =>
    apply Typing.tensor
    · simp ; exact hf
    · exact hneq
    · rw [Env.substTypes_preserves_disjoint]
      exact hDisj
    · exact ih

  case parr hf hneq _ ih =>
    apply Typing.parr
    · simp ; exact hf
    · exact hneq
    · exact ih

  case cut hf hneq hDisj _ ih =>
    apply Typing.cut
    · simp ; exact hf
    · exact hneq
    · rw [Env.substTypes_preserves_disjoint]
      exact hDisj
    · rw [HyperEnv.merge_assoc]
      · exact ih
