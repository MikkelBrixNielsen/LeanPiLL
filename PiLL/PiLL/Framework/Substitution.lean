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










-- FIXME: Notation for opening a proc at some depth not just 0
-- FIXME: Typing_preserves_proc_congr

-- FIXME: Fix ProcStep, EnvStep and TypingStep
-- FIXME: Instantiation / Opening Lemma
  -- ⊢ P⸨#w⸩ ∷ 𝒢 → ⊢ P⸨#w⸩{z // w} :: 𝒢{w // z} by Typing_substNames (or similar)
-- FIXME: Subject reduction / simulation proof

-- FIXME: Proof showing substitution avoids capture
-- FIXME: Check possibility of no having exchange rules

-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }



-- #FIXME: Needs to be proven
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
















macro "split_names_pos " hxy:ident ", " proof:ident : tactic =>
`(tactic| (
  subst $hxy
  simp at ⊢ $proof
  exact $proof
  ))

macro "split_names_neg " ih:ident ", " huniq:ident : tactic =>
  `(tactic| (
    simp at $ih $huniq
    apply $ih
    intros T h
    rcases h with ⟨hL, hR⟩ | h
    · exact $huniq _ (Or.inl ⟨hL, rfl⟩)
    · exact $huniq _ (Or.inr h)
  ))

macro "split_names_neg_triple " ih:ident ", " huniq:ident ", " hneq:ident : tactic =>
  `(tactic| (
    simp at $ih $huniq
    rw [Proc.open_substNames_comm $hneq, FPName.subst_self_of_ne $hneq] at $ih:ident
    apply $ih
    intros T h
    rcases h with ⟨hLL, hLR⟩ | ⟨hRL, hRR⟩ | h
    · exact $huniq _ (Or.inl ⟨hLL, rfl⟩)
    · subst hRL hRR ; contradiction
    · exact $huniq _ (Or.inr h)
  ))

macro "split_names " x:term " eq " y:term " using "
  proof:ident ", " ih:ident ", " huniq:ident : tactic =>
  `(tactic| (
    by_cases hxy : $x = $y
    case pos => split_names_pos hxy, $proof
    case neg => split_names_neg $ih, $huniq
  ))


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
    apply Typing.one (ih (by simp))

  case bot hF _ _ ih =>
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
    obtain ⟨hz1, hz2, hz3⟩ := hz
    obtain ⟨hw1, hw2, hw3⟩ := hw
    specialize ih z w hz3 hw3 hneq
    · exact x
    · exact y
    · by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg =>
        simp [HyperEnv.merge] at ⊢ ih huniq
        rw [FPName.subst_self_of_ne hz2, FPName.subst_self_of_ne hw2,
            Proc.openCut_substNames_comm hz2 hw2] at ih
        apply ih
        intro Ξ h T hinΞ
        cases h with
        | inl hL => exact huniq Ξ (Or.inl hL) T hinΞ
        | inr hR =>
          simp at hR
          rcases hR with rfl | rfl
          all_goals
            simp at hinΞ
            rcases hinΞ with ⟨rfl, rfl⟩ | h
            · contradiction
            · exact huniq (Γ‚ Δ) (Or.inr rfl) T (by grind)

  case tensor hF _ L _ ih =>
    apply Typing.tensor (L ∪ {x} ∪ {y})
    · intros z hz
      simp at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      specialize ih z hz3
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg =>
        simp at ⊢ ih huniq
        rw [Proc.open_substNames_comm hz2, FPName.subst_self_of_ne hz2] at ih
        apply ih <;> (intros T h ; rcases h with ⟨rfl, rfl⟩ | h)
        · contradiction
        · exact huniq _ (Or.inr (Or.inl h))
        · exact huniq _ (Or.inl ⟨rfl, rfl⟩)
        · exact huniq _ (Or.inr (Or.inr h))

    · exact Env.fresh_substNames_binary hF huniq

  case parr A B hF _ L _ ih =>
    apply Typing.parr (L ∪ {x} ∪ {y})
    · intros z hz
      simp at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      specialize ih z hz3
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg => split_names_neg_triple ih, huniq, hz2
    · exact Env.fresh_substNames hF huniq

  case oplus₁ hlc hT ih =>
    apply Typing.oplus₁
    · exact hlc
    · split_names x eq y using hT, ih, huniq

  case oplus₂ A _ _ hlc hT ih =>
    apply Typing.oplus₂
    · exact hlc
    · split_names x eq y using hT, ih, huniq

  case amp A B _ hTP hTQ ihP ihQ =>
    apply Typing.amp
    · split_names x eq y using hTP, ihP, huniq
    · split_names x eq y using hTQ, ihQ, huniq

  case quest hT ih =>
    apply Typing.quest
    split_names x eq y using hT, ih, huniq

  case bang hServ hT ih =>
    apply Typing.bang
    · exact Env.serverUsable_substNames hServ
    · split_names x eq y using hT, ih, huniq

  case w hF _ hlc hT ih =>
    apply Typing.w
    · exact Env.fresh_substNames hF huniq
    · exact hlc
    · by_cases hxy : x = y
      case pos => split_names_pos hxy, hT
      case neg =>
        simp at ih huniq
        apply ih
        intros T h
        exact huniq T (Or.inr h)

  case c A _ L hT ih =>
    apply Typing.c (L ∪ {x} ∪ {y})
    · intro w hw
      simp at hw
      obtain ⟨hw1, hw2, hw3⟩ := hw
      specialize hT w hw3
      specialize ih w hw3 (x := x) (y := y)
      by_cases hxy : x = y
      case pos => split_names_pos hxy, hT
      case neg => split_names_neg_triple ih, huniq, hw2

  case exists_ B _ hlc hT ih =>
    apply Typing.exists_
    · exact hlc
    · split_names x eq y using hT, ih, huniq

  case forall_ ih =>
    apply Typing.forall_
    have := ih (x := x) (y := y)
    rw [Env.shiftTypes_substNames_comm]
    simp only [HyperEnv.substNames_distributes, Env.substNames_distributes,
      HyperEnv.substNames_nil] at this
    apply this
    simp at ⊢ huniq this
    intros T h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact huniq ∀․T (Or.inl ⟨rfl, rfl⟩)
    · have ⟨A, hinΓ, _⟩:= (Env.mem_shiftTypes_iff.mp h)
      exact huniq A (Or.inr hinΓ)

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

lemma Typing_substTypes {n k : Nat} {P : Proc} {𝒢 : HyperEnv} {A : Types} :
  Typing (n + 1) P 𝒢 → A.lc n → k ≤ n → Typing n (P{A // k}) (𝒢{A // k}) := by
  intro hT hlcA hk
  generalize heq : n + 1 = n' at hT
  induction hT generalizing n A k hk <;> try simp

  case mix₀ =>
    exact Typing.mix₀

  case mix hD _ _ _ ihP ihQ =>
    apply Typing.mix
    · exact HyperEnv.substTypes_preserves_disjoint hD
    · exact ihP hlcA hk heq
    · exact ihQ hlcA hk heq

  case one ih =>
    exact Typing.one (ih hlcA hk heq)

  case bot hF _ _ ih =>
    apply Typing.bot
    · rw [Env.substTypes_preserves_names]
      exact hF
    · exact ih hlcA hk heq

  case cut 𝒢' Γ Δ Q B n'' L hTP ih =>
    simp at ih
    subst heq
    apply Typing.cut (A := B{A // k}) L
    simp [HyperEnv.merge]
    intro x y hx hy hneq
    exact ih x y hx hy hneq (n := n) (k := k) (A := A) hlcA hk (by simp)

  case tensor L _ ih =>
    simp at ih
    apply Typing.tensor L
    · intro y hy
      exact ih y hy hlcA hk heq
    · simp_all

  case parr L _ ih =>
    simp at ih
    apply Typing.parr L
    · intro y hy
      exact ih y hy hlcA hk heq
    · simp_all

  case oplus₁ hlcB _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.oplus₁
    · exact Types.lc_subst_lc_eq_lc hlcB hlcA hk
    · exact 𝒟

  case oplus₂ hlc _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.oplus₂
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · exact 𝒟

  case amp ihP ihQ =>
    exact Typing.amp (ihP hlcA hk heq) (ihQ hlcA hk heq)

  case quest ih =>
    exact Typing.quest (ih hlcA hk heq)

  case bang his _ ih =>
    apply Typing.bang
    · exact Env.serverUsable_substTypes his
    · exact (ih hlcA hk heq)

  case w hF _ hlc _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.w
    · rw [Env.substTypes_preserves_names]
      exact hF
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · exact 𝒟

  case c L _ ih =>
    simp at ih
    apply Typing.c L
    intro x hx
    exact ih x hx hlcA hk heq

  case exists_ hlc _ ih =>
    have := ih hlcA hk heq
    subst heq
    apply Typing.exists_
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · simp [HasSubst.subst]
      rw [← Types.subst_comm_0]
      exact this

  case forall_ Γ P x B _ _ ih =>
    simp at ih
    have hk' : k + 1 ≤ n + 1 := by grind
    have := ih (Types.lc_shift_0 hlcA) hk' heq
    subst heq
    apply Typing.forall_
    simp [HasSubst.subst, HasShiftTypes.shift] at ⊢ this
    exact this

  case exchange_env hP ih =>
    simp at ih
    apply Typing.exchange_env
    · exact ih hlcA hk heq
    · exact Env.substTypes_preserves_perm hP

  case exchange_hyper hP ih =>
    apply Typing.exchange_hyper
    · exact ih hlcA hk heq
    · exact HyperEnv.substTypes_preserves_perm hP

  case ax hneq _ hlcB =>
    subst heq
    apply Typing.ax
    · exact hneq
    · exact Types.lc_subst_lc_eq_lc hlcB hlcA hk
