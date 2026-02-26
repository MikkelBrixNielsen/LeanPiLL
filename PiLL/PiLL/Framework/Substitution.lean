import PiLL.Framework.Model.Judgement

-- theorem Typing.subst_name (𝒢 : HyperEnv) (P : Proc) (𝒟 : ⊢ P ∷ 𝒢) (x z : PName)
--   (hFresh : x ∉ 𝒢.names) (hSafe : x ∉ P.boundNames) :
--   ⊢ (P{x // z}) ∷ (𝒢{x // z}) := by
--   induction 𝒟

--   case mix₀ =>
--     simp only [HyperEnv.substName_empty, Proc.substname_nil]
--     apply Typing.mix₀

--   case mix 𝒢' ℋ' _ _ hDisj 𝒟 ℰ ihP ihQ =>
--     rw [HyperEnv.names_distributes, Finset.notMem_union] at hFresh
--     simp only [← HyperEnv.substName_merge, ← Proc.substName_par]
--     have this :  (𝒢'.substName x z).disjoint (ℋ'.substName x z) := by
--       apply HyperEnv.substName_preserves_disjoint
--       · apply hDisj
--       · simp [HyperEnv.names] at ⊢ hFresh
--         exact hFresh
--     apply Typing.mix
--     · exact this
--     · apply ihP
--       · exact hFresh.1
--       · apply Proc.not_bound_par_left hSafe
--         intro hxQf
--         have hℋ' : x ∈ ℋ'.names := Typing.f_subset_names ℰ hxQf
--         exact hFresh.2 hℋ'
--     · apply ihQ
--       · exact hFresh.2
--       · apply Proc.not_bound_par_right hSafe
--         intro hxPf
--         have h𝒢' : x ∈ 𝒢'.names := Typing.f_subset_names 𝒟 hxPf
--         exact hFresh.1 h𝒢'

--   case ax =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton, Proc.substName_link]
--     split
--     · rename_i xp yp A hneq hxpz
--       apply Typing.ax
--       subst hxpz
--       simp
--       apply And.intro
--       · exact hneq.symm
--       · simp only [HyperEnv.names_singleton, Env.names_distributes,
--           Env.names_singleton] at hFresh
--         simp at hFresh
--         exact hFresh.1
--     · rename_i xp yp A hneq hxpnz
--       apply Typing.ax
--       simp only [HyperEnv.names_singleton, Env.names_distributes,
--           Env.names_singleton] at hFresh
--       split
--       · simp at ⊢ hFresh
--         intro h
--         apply hFresh.right
--         exact h.symm
--       · exact hneq

--   case one ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     split
--     all_goals
--       apply Typing.one
--       simp at ih ; apply ih
--       rw [HyperEnv.names_singleton, Env.names_singleton, Finset.mem_singleton] at hFresh
--       simp [hFresh] at hSafe
--       exact hSafe

--   case bot ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     · apply Typing.bot
--       all_goals (try
--         rename_i hf _ hxpz
--         subst hxpz
--         rw [Env.substName_eq_self_of_not_mem]
--         · exact hFresh.1
--         · exact hf)
--       · apply ih
--         · exact hFresh.1
--         · exact hSafe
--     · apply Typing.bot
--       all_goals (try
--         rename_i hf _ _
--         exact Env.not_mem_substName_intro hf hFresh.2.symm)
--       · apply ih
--         · exact hFresh.1
--         · exact hSafe

--   case oplus₁ ih | oplus₂ ih | quest ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     all_goals
--     · constructor
--       · simp_all
--         exact ih

--   case amp ihP ihQ =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ihP ihQ
--     simp [hFresh] at hSafe
--     rename_i Γ P' Q' xp A B D E
--     have hsubP := Typing.f_subset_names D
--     have hsubQ := Typing.f_subset_names E
--     simp only [HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at hsubP hsubQ
--     have this : x ∉ P'.boundNames ∧ x ∉ Q'.boundNames := by grind
--     specialize ihP hFresh this.1
--     specialize ihQ hFresh this.2
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton] at ihP ihQ
--     split
--     · apply Typing.amp <;> simp_all
--       · exact ihP
--       · exact ihQ
--     · apply Typing.amp <;> simp_all
--       · exact ihP
--       · exact ihQ

--   case bang h ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     all_goals
--     · apply Typing.bang
--       · simp_all
--         exact ih
--       · apply Env.serverUsable_substName
--         exact h

--   case w ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     · apply Typing.w
--       · rename_i hf _ h
--         rw [Env.substName_eq_self_of_not_mem]
--         · exact hFresh.1
--         · subst h
--           exact hf
--       · exact ih hFresh.1 hSafe
--     · apply Typing.w
--       · rename_i hf _ h
--         exact Env.not_mem_substName_intro hf hFresh.2.symm
--       · exact ih hFresh.1 hSafe

--   case c Γ P' xp yp A hneq hf D ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh, ← ne_eq] at hSafe
--     split_ifs
--     · simp_all
--     · apply Typing.c
--       · exact hSafe.1
--       · apply And.intro
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.1
--           · rename_i h1 h2
--             subst h1
--             exact hf.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2
--           · rename_i h1 h2
--             subst h1
--             exact hf.1
--       · rw [Env.substName_eq_self_of_not_mem]
--         · rename_i h1 h2
--           specialize ih ⟨hFresh, hSafe.1⟩ hSafe.2
--           simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--             Env.substName_singleton, h1, h2, if_true, if_false] at ih
--           rw [Env.substName_eq_self_of_not_mem] at ih
--           · exact ih
--           · subst h1
--             exact hf.1
--         · rename_i h1 h2
--           subst h1
--           exact hf.1
--     · apply Typing.c
--       · exact hneq
--       · apply And.intro
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.1
--           · rename_i h1 h2
--             subst h2
--             exact hf.2
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2
--           · rename_i h1 h2
--             subst h2
--             exact hf.2
--       · rename_i h1 h2
--         rw [Env.substName_eq_self_of_not_mem]
--         · exact D
--         · subst h2
--           exact hf.2
--     · apply Typing.c
--       · exact hneq
--       · apply And.intro
--         · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
--         · exact Env.not_mem_substName_intro hf.2 hSafe.1.symm
--       · rename_i h1 h2
--         specialize ih ⟨hFresh, hSafe.1⟩ hSafe.2
--         simp [h1, h2]at ih
--         exact ih

--   case exists_ Γ P' xp A B X D ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     · apply Typing.exists_
--       rename_i h
--       subst h
--       simp at ⊢ ih hFresh
--       apply ih hFresh.1 hFresh.2
--       exact hSafe
--     · apply Typing.exists_
--       rename_i h
--       specialize ih hFresh hSafe
--       simp [h] at ih
--       exact ih

--   case forall_ h ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh ih
--     simp [hFresh] at hSafe
--     split
--     all_goals
--     · apply Typing.forall_
--       · simp_all
--         apply ih
--       · rw [Env.ft_substName_eq_self]
--         exact h

--   case tensor hf hneq hDisj h ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh
--     simp [hFresh, ← ne_eq] at hSafe
--     split_ifs with h1 h2 h3
--     · rw [h1, h2] at hneq
--       contradiction
--     · apply Typing.tensor
--       · apply And.intro
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.1.1
--           · subst h1 ; exact hf.1
--         · apply And.intro
--           · rw [Env.substName_eq_self_of_not_mem]
--             · exact hFresh.1.2
--             · subst h1 ; exact hf.2.1
--           · apply And.intro
--             · rw [Env.substName_eq_self_of_not_mem]
--               · exact hf.2.2.1
--               · subst h1 ; exact hf.1
--             · rw [Env.substName_eq_self_of_not_mem]
--               · exact hf.2.2.2
--               · subst h1 ; exact hf.2.1
--       · exact hSafe.1
--       · apply Env.substName_preserves_disjoint
--         · exact hDisj
--         · exact hFresh.1
--       · simp only [← HyperEnv.substName_merge, HyperEnv.substName_singleton,
--           Env.substName_distributes, Env.substName_singleton, h1, h2, if_false,
--           if_true] at ih
--         apply ih
--         · simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--             Env.names_distributes, Env.names_singleton, Finset.notMem_union,
--             Finset.mem_singleton, ← ne_eq]
--           apply And.intro
--           · exact And.intro hFresh.1.1 hSafe.1
--           · exact And.intro hFresh.1.2 (by subst h1 ; exact hFresh.2)
--         · exact hSafe.2
--     · apply Typing.tensor
--       · apply And.intro
--         · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
--         · apply And.intro
--           · rw [Env.substName_eq_self_of_not_mem]
--             · exact hf.2.1
--             · subst h3 ; exact hf.2.2.2
--           · apply And.intro
--             · rw [Env.substName_eq_self_of_not_mem]
--               · exact hf.2.2.1
--               · subst h3 ; exact hf.2.2.1
--             · rw [Env.substName_eq_self_of_not_mem]
--               · exact hf.2.2.2
--               · subst h3 ; exact hf.2.2.2
--       · exact hneq
--       · apply Env.substName_preserves_disjoint
--         · exact hDisj
--         · exact hFresh.1
--       · repeat rw [Env.substName_eq_self_of_not_mem]
--         · exact h
--         · subst h3 ; exact hf.2.2.2
--         · subst h3 ; exact hf.2.2.1
--     · apply Typing.tensor
--       · apply And.intro
--         · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
--         · apply And.intro
--           · exact Env.not_mem_substName_intro hf.2.1 hFresh.2.symm
--           · apply And.intro
--             · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.1.symm
--             · exact Env.not_mem_substName_intro hf.2.2.2 hSafe.1.symm
--       · exact hneq
--       · apply Env.substName_preserves_disjoint
--         · exact hDisj
--         · exact hFresh.1
--       · simp only [← HyperEnv.substName_merge, HyperEnv.substName_singleton,
--           Env.substName_distributes, Env.substName_singleton, h1, h3, if_false] at ih
--         apply ih
--         · simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--             Env.names_distributes, Env.names_singleton, Finset.notMem_union,
--             Finset.mem_singleton, ← ne_eq]
--           apply And.intro
--           · exact ⟨hFresh.1.1, hSafe.1⟩
--           · exact ⟨hFresh.1.2, hFresh.2⟩
--         · exact hSafe.2

--   case parr hf hneq h ih =>
--     simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--       Env.substName_singleton]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at hFresh
--     simp [hFresh, ← ne_eq] at hSafe
--     split_ifs with h1 h2 h3
--     · apply Typing.parr
--       · apply And.intro
--         · rw [h1, h2] at hneq
--           contradiction
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2
--           · subst h2 ; exact hf.2
--       · exact hSafe.1
--       · rw [h1, h2] at hneq
--         contradiction
--     · apply Typing.parr
--       · apply And.intro
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.1
--           · subst h1 ; exact hf.1
--         · apply Env.not_mem_substName_intro hf.2 hSafe.1.symm
--       · exact hSafe.1
--       · simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--           Env.substName_singleton, h1, h2, if_true, if_false] at ih
--         apply ih
--         · simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--             Finset.notMem_union, Finset.mem_singleton]
--           exact ⟨⟨hFresh.1, hSafe.1⟩, (by subst h1 ; exact hFresh.2)⟩
--         · exact hSafe.2
--     · apply Typing.parr
--       · apply And.intro
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.1
--           · subst h3 ; exact hf.2
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2
--           · subst h3 ; exact hf.2
--       · exact hneq
--       · rw [Env.substName_eq_self_of_not_mem]
--         · exact h
--         · subst h3 ; exact hf.2
--     · apply Typing.parr
--       · apply And.intro
--         · exact Env.not_mem_substName_intro hf.1 hFresh.2.symm
--         · exact Env.not_mem_substName_intro hf.2 hSafe.1.symm
--       · exact hneq
--       · simp only [HyperEnv.substName_singleton, Env.substName_distributes,
--           Env.substName_singleton, h1, h3, if_false] at ih
--         apply ih
--         · simp only [HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--             Finset.notMem_union, Finset.mem_singleton, ← ne_eq]
--           exact ⟨⟨hFresh.1, hSafe.1⟩, hFresh.2⟩
--         · exact hSafe.2

--   case cut 𝒢' Γ' Δ' P' xp yp A hf hneq hDisj h ih =>
--     simp only [HyperEnv.substName_distributes, HyperEnv.substName_singleton,
--       Env.substName_distributes]
--     conv_rhs => simp [HasSubst.subst, Proc.substName]
--     simp only [HyperEnv.names_distributes, HyperEnv.names_singleton, Env.names_distributes,
--       Finset.notMem_union] at hFresh
--     simp [← ne_eq] at hSafe
--     simp only [HyperEnv.substName_distributes, HyperEnv.substName_singleton,
--       Env.substName_distributes, Env.substName_singleton, HyperEnv.names_distributes,
--       HyperEnv.names_singleton, Env.names_distributes, Env.names_singleton,
--       Finset.notMem_union, Finset.mem_singleton, ← ne_eq] at ih
--     split_ifs with h1 h2 h3 h4
--     · apply Typing.cut
--       · split_ands
--         · exact HyperEnv.not_mem_substName_intro hf.1 hSafe.2.1
--         · exact Env.not_mem_substName_intro hf.2.1  hSafe.2.1.symm
--         · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.2.1.symm
--         · exact HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
--       · exact hneq
--       · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
--       · rcases h1 with rfl | rfl
--         all_goals
--         · rw [HyperEnv.substName_eq_self_of_not_mem]
--           · rw [Env.substName_eq_self_of_not_mem]
--             · rw [Env.substName_eq_self_of_not_mem]
--               · exact h
--               · try exact hf.2.2.1
--                 try exact hf.2.2.2.2.2
--             · try exact hf.2.1
--               try exact hf.2.2.2.2.1
--           · try exact hf.1
--             try exact hf.2.2.2.1
--     · simp [← ne_eq] at h1
--       subst h2 h3
--       contradiction
--     · apply Typing.cut
--       · split_ands
--         · rw [HyperEnv.substName_eq_self_of_not_mem]
--           · exact hFresh.1
--           · subst h2 ; exact hf.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.2.1
--           · subst h2 ; exact hf.2.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.2.2
--           · subst h2 ; exact hf.2.2.1
--         · exact HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
--       · exact hSafe.1
--       · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
--       · simp only [h2, h3, if_true, if_false] at ih
--         apply ih
--         · subst h2
--           exact ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩
--         · exact hSafe.2.2

--     · apply Typing.cut
--       · split_ands
--         · rw [HyperEnv.substName_eq_self_of_not_mem]
--           · exact hf.1
--           · subst h4 ; exact hf.2.2.2.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2.1
--           · subst h4 ; exact hf.2.2.2.2.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hf.2.2.1
--           · subst h4 ; exact hf.2.2.2.2.2
--         · rw [HyperEnv.substName_eq_self_of_not_mem]
--           · exact hFresh.1
--           · subst h4 ; exact hf.2.2.2.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.2.1
--           · subst h4 ; exact hf.2.2.2.2.1
--         · rw [Env.substName_eq_self_of_not_mem]
--           · exact hFresh.2.2
--           · subst h4 ; exact hf.2.2.2.2.2
--       · exact hSafe.2.1.symm
--       · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
--       · simp only [h2, h4, if_true, if_false] at ih
--         apply ih
--         · subst h4
--           exact ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩
--         · exact hSafe.2.2
--     · apply Typing.cut
--       · split_ands
--         · exact HyperEnv.not_mem_substName_intro hf.1 hSafe.2.1
--         · exact  Env.not_mem_substName_intro hf.2.1 hSafe.2.1.symm
--         · exact Env.not_mem_substName_intro hf.2.2.1 hSafe.2.1.symm
--         · apply HyperEnv.not_mem_substName_intro hf.2.2.2.1 hSafe.1
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.1 hSafe.1.symm
--         · exact Env.not_mem_substName_intro hf.2.2.2.2.2 hSafe.1.symm
--       · exact hneq
--       · exact Env.substName_preserves_disjoint hDisj ⟨hFresh.2.1, hFresh.2.2⟩
--       · simp only [h2, h4, if_false] at ih
--         apply ih ⟨⟨hFresh.1, ⟨hFresh.2.1, hSafe.2.1⟩⟩, ⟨hFresh.2.2, hSafe.1⟩⟩ hSafe.2.2


-- lemma Types.subst_commute {T A B : Types} {X Y : TVar} {hne : Y ≠ X} {hft : Y ∉ A.freeTypes} :
--   (T.subst B Y).subst A X = (T.subst A X).subst (B.subst A X) Y := by
--   induction T generalizing A B X Y <;> simp_all [Types.subst]

--   case var =>
--     split_ifs <;> simp_all [Types.subst]

--   case varDual =>
--     split_ifs
--     · simp_all
--     · simp_all [Types.subst]
--       erw [← Types.subst_dual]
--       rfl
--     · simp_all [Types.subst]
--       symm
--       apply Types.subst_eq_self_of_not_mem
--       simp [Types.freeTypes_dual_eq, hft]
--     · simp_all [Types.subst]

--   case forall_ ih =>
--     split_ifs with h1 h2 h3 <;> simp_all [Types.subst]
--     sorry -- FIXME: Generally false, but true assuming Barendregt's variable convention

--   case exist_ =>
--     split_ifs with h1 h2 h3 <;> try simp_all [Types.subst]
--     sorry -- FIXME: Generally false, but true assuming Barendregt's variable convention

-- theorem Typing.subst_types {𝒢 : HyperEnv} {P : Proc} {𝒟 : ⊢ P ∷ 𝒢}
--   {A : Types} {X : TVar} : ⊢ (P{A // X}) ∷ (𝒢{A // X}) := by
--   induction 𝒟 <;> simp [-Finset.singleton_union, -Finset.union_singleton] at *

--   case mix₀ => apply Typing.mix₀

--   case ax hneq =>
--     apply Typing.ax
--     exact hneq

--   case mix hDisj _ _ ihP ihQ =>
--     apply Typing.mix
--     · simp [HyperEnv.substTypes_preserves_disjoint]
--       exact hDisj
--     · exact ihP
--     · exact ihQ

--   case one ih =>
--     apply Typing.one
--     · exact ih

--   case bot hf _ ih =>
--     apply Typing.bot
--     · simp ; exact hf
--     · apply ih

--   case oplus₁ ih =>
--     apply Typing.oplus₁
--     exact ih

--   case oplus₂ ih =>
--     apply Typing.oplus₂
--     exact ih

--   case quest ih =>
--     apply Typing.quest
--     exact ih

--   case amp ihP ihQ =>
--     constructor
--     · exact ihP
--     · exact ihQ

--   case c hneq hf _ ih =>
--     apply Typing.c
--     · exact hneq
--     · simp ; exact hf
--     · exact ih

--   case w hf _ ih =>
--     apply Typing.w
--     · simp ; exact hf
--     · apply ih

--   case bang hsu ih =>
--     all_goals
--       apply Typing.bang
--       · exact ih
--       · apply Env.serverUsable_substTypes
--         exact hsu

--   case exists_ ih =>
--     simp [HasSubst.subst, Types.subst] at ⊢ ih
--     split_ifs with h
--     · apply Typing.exists_
--       simp_all only [HasSubst.subst, Types.subst_subst]
--     · apply Typing.exists_
--       rw [Types.subst_commute] at ih
--       · exact ih
--       · exact h
--       · sorry -- FIXME: Currently assuming Barendregt

--   case forall_ D ft ih =>
--     conv_lhs => rhs ; rhs ; simp [HasSubst.subst, Types.subst]
--     split_ifs with h
--     · subst h
--       rw [Proc.substTypes_input_match]
--       apply Typing.forall_
--       · rw [Env.substTypes_eq_self_of_not_mem]
--         · exact D
--         · exact ft
--       · rw [Env.substTypes_eq_self_of_not_mem]
--         · exact ft
--         · exact ft
--     · rw [Proc.substTypes_input_diff]
--       · apply Typing.forall_
--         · apply ih
--         · apply Env.not_mem_ft_substTypes
--           · exact ft
--           · sorry -- FIXME: Currently assuming Barendregt
--           · exact h
--       · exact h

--   case tensor hf hneq hDisj _ ih =>
--     apply Typing.tensor
--     · simp ; exact hf
--     · exact hneq
--     · rw [Env.substTypes_preserves_disjoint]
--       exact hDisj
--     · exact ih

--   case parr hf hneq _ ih =>
--     apply Typing.parr
--     · simp ; exact hf
--     · exact hneq
--     · exact ih

--   case cut hf hneq hDisj _ ih =>
--     apply Typing.cut
--     · simp ; exact hf
--     · exact hneq
--     · rw [Env.substTypes_preserves_disjoint]
--       exact hDisj
--     · rw [HyperEnv.merge_assoc]
--       · exact ih

@[simp] lemma FPName.subst_id {x z : FPName} :
  z{x // x} = z := by
  simp [HasSubst.subst, FPName.subst]
  intro h
  apply h.symm



@[simp] lemma Channel.subst_self {u : Channel} {x : FPName} :
  u.subst x x = u := by
  induction u generalizing x <;> simp_all [Channel.subst]

@[simp] lemma Channel.subst_self_notation {u : Channel} {x : FPName} :
  u{x // x} = u := by
  induction u generalizing x <;> simp_all [HasSubst.subst, Channel.subst]






@[simp] lemma Proc.substNames_self {P : Proc} {x : FPName} :
  P{x // x} = P := by
  induction P generalizing x <;> simp_all [HasSubst.subst, Proc.substNames]



macro "simp_Proc_substNames" : tactic =>
  `(tactic|
    (simp [HasSubst.subst, Proc.substNames, Channel.subst, FPName.subst] ;
      try (split_ifs <;> try constructor <;> rfl)))

@[simp] lemma Proc.substNames_cut {P : Proc} {x y : FPName} :
  (𝑣⸨#,#⸩P){y // x} = 𝑣⸨#,#⸩P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_tensor {P : Proc} {x y z : FPName} :
  (#z⟦#N⟧․P){y // x} = #z{y // x}⟦#N⟧․P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_parr {P : Proc} {x y z : FPName} :
  (#z⸨#N⸩․P){y // x} = #z{y // x}⸨#N⸩․P{y // x} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_oplus₁ {P : Proc} {x y z : FPName} :
  (#z⟦𝐋⟧․P){y // x} = (#z{y // x}⟦𝐋⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_oplus₂ {P : Proc} {x y z : FPName} :
  (#z⟦𝐑⟧․P){y // x} = (#z{y // x}⟦𝐑⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_amp {P Q : Proc} {x y z : FPName} :
  #z․case{𝐋 : P, 𝐑 : Q}{y // x} = #z{y // x}․case{𝐋 : P{y // x}, 𝐑 : Q{y // x}} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_quest {P : Proc} {x y z : FPName} :
  (#z⟦USE⟧․P){y // x} = (#z{y // x}⟦USE⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_bang {P : Proc} {x y z : FPName} :
  !#z․{P}{y // x} = !#z{y // x}․{P{y // x}} := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_w {P : Proc} {x y z : FPName} :
  (#z⟦DISP⟧․P){y // x} = (#z{y // x}⟦DISP⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_c {P : Proc} {x y z : FPName} :
  (#z⟦DUP⟧⸨#N⸩․P){y // x} = (#z{y // x}⟦DUP⟧⸨#N⸩․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_exists {P : Proc} {x y z : FPName} {A : Types} :
  (#z⟦A⟧․P){y // x} = (#z{y // x}⟦A⟧․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_forall {P : Proc} {x y z : FPName} :
  (#z⸨#T⸩․P){y // x} = (#z{y // x}⸨#T⸩․P{y // x}) := by
  simp_Proc_substNames

@[simp] lemma Proc.substNames_ax {w x y z : FPName} :
  (#w⟷ₚ#z){y // x} = (#w{y // x}⟷ₚ#z{y // x}) := by
  simp_Proc_substNames




lemma Proc.open_substNames_comm {P : Proc} {x y z : FPName} (hneq : z ≠ x) :
  P⸨#z⸩{y // x} = P{y // x}⸨#z⸩ := by
  induction P
  case nil => simp [Proc.open0, Proc.open, HasSubst.subst, Proc.substNames]
  case one => sorry
  all_goals sorry

lemma Proc.openCut_substNames_comm {P : Proc} {x y z w : FPName} (hFz : z ≠ x) (hFw : w ≠ x) :
  P⸨#z, #w⸩{y // x} = P{y // x}⸨#z, #w⸩ := by
  induction P
  all_goals sorry











@[simp] lemma Env.substNames_self {Γ : Env} {x : FPName} :
  Γ{x // x} = Γ := by
  induction Γ generalizing x <;> simp_all [HasSubst.subst, Env.substNames]
  case cons hd tl ih =>
    intro h
    obtain ⟨hd1, hd2⟩ := hd
    simp_all

@[simp] lemma Env.not_mem_names_iff {Γ : Env} {x : FPName} :
  x ∉ Γ.names ↔ ∀ A, (x, A) ∉ Γ := by
  simp [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.not_mem_names_cons {Γ : Env} {E : Elem} {x : FPName} :
  x ∉ Env.names (E :: Γ) ↔ x ≠ E.1 ∧ x ∉ Γ.names := by
  simp_all
  constructor
  · intro h
    simp_all
    obtain ⟨E1, E2⟩ := E
    specialize h E2
    simp_all
  · intro A
    obtain ⟨E1, E2⟩ := E
    simp_all

@[simp] lemma Env.substNames_of_not_mem {Γ : Env} {x y : FPName} :
  x ∉ Γ.names → Γ{y // x} = Γ := by
  intro hF
  induction Γ
  case nil => simp
  case cons E Γ ih =>
    cases E
    case mk z A =>
      have : x ≠ z := by
        simp at hF
        specialize hF A
        simp_all
      simp
      constructor
      · apply FPName.subst_self_of_ne (this.symm)
      · exact ih (hF := by simp_all)


lemma Env.substNames_preserves_Types {Γ : Env} {x y : FPName} :
  ∀ z A, (z, A) ∈ Γ → (z{y // x}, A) ∈ Γ{y // x} := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]
  intro z A hMem
  use z, A
  simp_all
  split_ifs <;> rfl

lemma Env.mem_serverUsable_Types {Γ : Env} {x : FPName} {A : Types} :
  ?ₑΓ → (x, A) ∈ Γ → A.isServerUsable := by
  intro hServ hMem
  simp [Env.serverUsable] at hServ
  exact hServ x A hMem


lemma Env.serverUsable_substNames {Γ : Env} {x y : FPName} :
  ?ₑΓ → ?ₑΓ{y // x} := by
  intro hServ
  simp [HasSubst.subst, Env.substNames, Env.serverUsable]
  intros z A w B hMem
  split_ifs <;> intro h <;> (
    simp_all
    exact Env.mem_serverUsable_Types hServ hMem
  )

lemma Env.substNames_preserves_perm {Γ Δ : Env} {x y : FPName} :
  Γ ~ Δ → Γ{y // x} ~ Δ{y // x} := by
  simp_all [HasSubst.subst, Env.substNames]
  grind

@[simp] lemma Env.shiftTypes_substNames_comm {Γ : Env} {x y : FPName} :
  (Γ{y // x})⁺ᵗ = (Γ⁺ᵗ){y // x} := by
  simp_all [HasSubst.subst, Env.substNames, HasShiftTypes.shift, Env.shiftTypes]
  intros ; split_ifs <;> rfl

lemma Env.mem_shiftTypes_iff {Γ : Env} {y : FPName} {T : Types} :
  (y, T) ∈ Γ⁺ᵗ ↔ ∃ A, (y, A) ∈ Γ ∧ T = A⁺ᵗ := by
  induction Γ
  case nil => simp
  case cons hd tl ih =>
    match hd with
    | (x, B) => simp_all ; grind


macro "fresh_substNames_binary_aux"
  z:term ", " C:term ", " Γ:term ", " Δ:term ", " huniq:term: tactic =>
  `(tactic| (
    intro Ξ hin T hMem
    simp at hin; subst hin
    simp at hMem
    rcases hMem with ⟨hyz, rfl⟩ | hin
    · exact $huniq ($z ∶ $C :: $Γ ++ $Δ) (by simp) $C (by simp [hyz])
    · apply $huniq ($z ∶ $C :: $Γ ++ $Δ) (by simp) T
      simp
      right ; left ; exact hin
      simp
  ))

lemma Env.fresh_substNames_binary {Γ Δ : Env} {x y z : FPName} {C : Types}
  (hF : z ∉ Γ.names ∧ z ∉ Δ.names)
  (huniq : ∀ Γ_1 ∈ [z ∶ C :: Γ ++ Δ], ∀ (T : Types), (y, T) ∈ Γ_1 → y = x) :
  z{y // x} ∉ Γ{y // x}.names ∧ z{y // x} ∉ Δ{y // x}.names := by
  cases hF
  case intro hFΓ hFΔ =>
  constructor
  · exact Env.fresh_substNames hFΓ (A := C) (by simp_all ; grind)
  · exact Env.fresh_substNames hFΔ (A := C) (by simp_all ; grind)










@[simp] lemma HyperEnv.substNames_self {𝒢 : HyperEnv} {x : FPName} :
  𝒢{x // x} = 𝒢 := by induction 𝒢 generalizing x <;> simp_all

@[simp] lemma HyperEnv.substNames_of_not_mem {𝒢 : HyperEnv} {x : FPName} :
  x ∉ 𝒢.names → (𝒢{x // x} = 𝒢) := by induction 𝒢 <;> simp

lemma HyperEnv.substNames_preserves_perm {𝒢 ℋ : HyperEnv} {x y : FPName} :
  𝒢 ~ ℋ → 𝒢{y // x} ~ ℋ{y // x} := by
  simp_all [HasSubst.subst, HyperEnv.substNames]
  grind


-- macro "split_names " x:term " eq " y:term " using " ih:ident : tactic =>
--   `(tactic| (
--     by_cases hxy : $x = $y
--     case pos =>
--       simp_all
--     case neg =>
--       simp at $ih:ident
--       grind [FPName.subst_self_of_ne, Proc.open_substNames_comm,
--         Env.shiftTypes_substNames_comm]
--   ))


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }


-- Condition: y is not already in G (unless y = x, which is a no-op)
lemma Typing_substNames {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x y : FPName} :
  Typing n P 𝒢 → (∀ Γ ∈ 𝒢, ∀ A, (y, A) ∈ Γ → y = x) →
  Typing n (P{y // x}) (𝒢{y // x}) := by
  intro hT huniq
  induction hT generalizing x y <;> try simp

  case mix₀ => apply Typing.mix₀

  case mix hD _ _ _ ihP ihQ =>
    apply Typing.mix
    · apply HyperEnv.substNames_preserves_disjoint
      · exact hD
      · exact huniq
    · apply ihP
      intros Γ hin𝒢 T hinΓ
      exact huniq Γ (by simp ; apply Or.inl hin𝒢) T hinΓ
    · apply ihQ
      intros Γ hin𝒢 T hinΓ
      exact huniq Γ (by simp ; apply Or.inr hin𝒢) T hinΓ

  case one ih =>
    apply Typing.one
    apply ih
    simp

  case bot Γ' P' z hF n' hT ih =>
    apply Typing.bot
    · exact Env.fresh_substNames hF huniq
    · apply ih
      intros Γ hΓ T hinΓ
      simp at huniq hΓ
      subst hΓ
      exact huniq T (Or.inr hinΓ)

  case cut Γ Δ _ A _ L _ ih =>
    apply Typing.cut (A := A) (L ∪ {x} ∪ {y})
    intros z w hz hw hneq
    simp at hz hw
    specialize ih z w hz.2.2 hw.2.2 hneq
    · exact x
    · exact y
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp at ⊢ ih
        exact ih
      case neg =>
        simp [HyperEnv.merge] at ⊢ ih huniq
        rw [FPName.subst_self_of_ne hz.2.1, FPName.subst_self_of_ne hw.2.1,
            Proc.openCut_substNames_comm hz.2.1 hw.2.1] at ih
        apply ih
        intros Ξ hOr B hinΞ
        cases hOr with
        | inl hL => exact huniq Ξ (Or.inl hL) B hinΞ
        | inr hR =>
          simp at hR
          cases hR with
          | inl h =>
            subst h
            simp at hinΞ
            cases hinΞ with
            | inl h =>
              obtain ⟨hL, hR⟩ := h
              subst hL hR
              exfalso
              apply hz.1 rfl
            | inr h =>
              exact huniq (Γ‚ Δ) (Or.inr rfl) B (by simp ; exact Or.inl h)
          | inr h =>
            subst h
            simp at hinΞ
            cases hinΞ with
            | inl h =>
              obtain ⟨hL, hR⟩ := h
              subst hL hR
              exfalso
              apply hw.1 rfl
            | inr h =>
              exact huniq (Γ‚ Δ) (Or.inr rfl) B (by simp ; apply Or.inr h)

  case tensor A B hF _ L _ ih =>
    apply Typing.tensor (L ∪ {x} ∪ {y})
    · intros z hz
      simp at hz
      specialize ih z hz.2.2
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos =>
        subst hxy
        simp at ⊢ ih
        exact ih
      case neg =>
        simp at ⊢ ih huniq
        rw [Proc.open_substNames_comm hz.2.1, FPName.subst_self_of_ne hz.2.1] at ih
        apply ih
        · intros T h
          cases h with
          | inl h =>
            rw [h.1] at hz
            exfalso
            apply hz.1 rfl
          | inr h => exact huniq T (Or.inr (Or.inl h))
        · intros T h
          cases h with
          | inl h =>
            obtain ⟨hL, hR⟩ := h
            subst hL hR
            exact huniq (B ⨂ T) (Or.inl (And.intro rfl rfl))
          | inr h => exact huniq T (Or.inr (Or.inr h))
    · exact Env.fresh_substNames_binary hF huniq

  case parr A B hF _ L _ ih =>
    apply Typing.parr (L ∪ {x} ∪ {y})
    · intros z hz
      simp at hz
      specialize ih z hz.2.2
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos =>
        subst hxy
        simp at ⊢ ih
        exact ih
      case neg =>
        simp at ih huniq
        rw [Proc.open_substNames_comm hz.2.1, FPName.subst_self_of_ne hz.2.1] at ih
        apply ih
        intros T h
        cases h with
        | inl h =>
          obtain ⟨hL, hR⟩ := h
          subst hL hR
          exact  huniq (A ⅋ T) (Or.inl (And.intro rfl rfl))
        | inr h =>
          cases h with
          | inl h =>
            obtain ⟨hL, hR⟩ := h
            subst hL hR
            exfalso
            apply hz.1 rfl
          | inr h => exact huniq T (Or.inr h)
    · exact Env.fresh_substNames hF huniq

  case oplus₁ B _ hlc hT ih =>
    apply Typing.oplus₁
    · exact hlc
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        obtain ⟨hL, hR⟩ := h
        case inl =>
          subst hL hR
          exact huniq (T ⊕ B) (Or.inl (And.intro rfl rfl))
        case inr h => exact huniq T (Or.inr h)

  case oplus₂ A _ _ hlc hT ih =>
    apply Typing.oplus₂
    · exact hlc
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        obtain ⟨hL, hR⟩ := h
        case inl =>
          subst hL hR
          exact huniq (A ⊕ T) (Or.inl (And.intro rfl rfl))
        case inr h => exact huniq T (Or.inr h)

  case amp A B _ hTP hTQ ihP ihQ =>
    apply Typing.amp
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hTP
      case neg =>
        simp at ihP huniq
        apply ihP
        intros T h
        cases h with
        | inl h =>
          obtain ⟨hL, hR⟩ := h
          subst hL hR
          exact huniq (T & B) (Or.inl (And.intro rfl rfl))
        | inr h => exact huniq T (Or.inr h)
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hTQ
      case neg =>
        simp at ihQ huniq
        apply ihQ
        intros T h
        cases h with
        | inl h =>
          obtain ⟨hL, hR⟩ := h
          subst hL hR
          exact huniq (A & T) (Or.inl (And.intro rfl rfl))
        | inr h => exact huniq T (Or.inr h)

  case quest hT ih =>
    apply Typing.quest
    by_cases hxy : x = y
    case pos =>
      subst hxy
      simp
      exact hT
    case neg =>
      simp at ih huniq
      apply ih
      intros T h
      obtain ⟨hL, hR⟩ := h
      case inl =>
        subst hL hR
        exact huniq (??T) (Or.inl (And.intro rfl rfl))
      case inr h =>
        exact huniq T (Or.inr h)

  case bang hServ hT ih =>
    apply Typing.bang
    · exact Env.serverUsable_substNames hServ
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        obtain ⟨hL, hR⟩ := h
        case inl =>
          subst hL hR
          exact huniq (!!T) (Or.inl (And.intro rfl rfl))
        case inr h => exact huniq T (Or.inr h)

  case w hF _ hlc hT ih =>
    apply Typing.w
    · exact Env.fresh_substNames hF huniq
    · exact hlc
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        exact huniq T (Or.inr h)

  case c A _ L hT ih =>
    apply Typing.c (L ∪ {x} ∪ {y})
    · intro w hw
      simp at hw
      specialize ih w hw.2.2 (x := x) (y := y)
      by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT w hw.2.2
      case neg =>
        simp at ih huniq
        rw [Proc.open_substNames_comm hw.2.1, FPName.subst_self_of_ne hw.2.1] at ih
        apply ih
        intros T h
        cases h
        case inl h =>
          obtain ⟨hL, hR⟩ := h
          subst hL hR
          exact huniq (??A) (Or.inl (And.intro rfl rfl))
        case inr h =>
          cases h
          case inl h =>
            obtain ⟨hL, hR⟩ := h
            subst hL hR
            exfalso
            apply hw.1 rfl
          case inr h => exact huniq T (Or.inr h)

  case exists_ B _ hlc hT ih =>
    apply Typing.exists_
    · exact hlc
    · by_cases hxy : x = y
      case pos =>
        subst hxy
        simp
        exact hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        cases h
        case inl h =>
          obtain ⟨hL, hR⟩ := h
          subst hL hR
          exact huniq (∃․B) (Or.inl (And.intro rfl rfl))
        case inr h => exact huniq T (Or.inr h)

  case forall_ ih =>
    apply Typing.forall_
    have := ih (x := x) (y := y)
    rw [Env.shiftTypes_substNames_comm]
    simp only [HyperEnv.substNames_distributes, Env.substNames_distributes,
      HyperEnv.substNames_nil] at this
    apply this
    simp at ⊢ huniq this
    intros T hOr
    cases hOr with
    | inl hL =>
      obtain ⟨hy, hT⟩ := hL
      subst hy hT
      exact huniq ∀․T (Or.inl ⟨rfl, rfl⟩)
    | inr hin =>
      obtain ⟨A, hL, hR⟩ := Env.mem_shiftTypes_iff.mp hin
      exact huniq A (Or.inr hL)

  case exchange_env hP ih =>
    apply Typing.exchange_env
    · apply ih
      intros Γ hΓ T hinΓ
      simp at huniq
      cases hΓ with
      | head => exact huniq.1 T ((List.Perm.mem_iff (a := (y, T)) hP).mp hinΓ)
      | tail _ hin𝒢 => exact huniq.2 Γ hin𝒢 T hinΓ
    · exact Env.substNames_preserves_perm hP

  case exchange_hyper hP ih =>
    apply Typing.exchange_hyper
    · apply ih
      intros Γ hΓ T hinΓ
      exact huniq Γ ((List.Perm.mem_iff (a := Γ) hP).mp hΓ) T hinΓ
    · apply HyperEnv.substNames_preserves_perm hP

  case ax A hneq _ hlc =>
    apply Typing.ax
    · simp [HasSubst.subst, FPName.subst]
      split_ifs <;> (by_contra ; simp at huniq)
      case pos h1 h2 h3 =>
        subst h1 h2
        apply hneq rfl
      case neg h1 h2 h3 =>
        have := huniq A (Or.inr (And.intro h3 rfl))
        subst this
        exact h2 h3.symm
      case pos h1 h2 h3 =>
        have := huniq Aᗮ (Or.inl (And.intro h3.symm rfl))
        subst this
        exact h1 h3
      case neg h1 h2 h3 =>
        exact hneq h3
    · exact hlc
