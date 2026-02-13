import PiLL.Framework.Model.Environment
-- import PiLL.Framework.Model.Alpha
-- import PiLL.Framework.Model.Congruence

-- FIXME: Added a lot of extra contranints so facilitate Env / HyperEnv disjointness
-- as well as no pathological process appearing e.g. x(x).P, x[DUP](x).P etc.

-- inductive Typing : HyperEnv → Proc → Prop where
--   | mix₀ :
--       ----------
--       Typing ∅ 𝟘

--   | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {hDisj : 𝒢.disjoint ℋ}:
--       Typing 𝒢 P → Typing ℋ Q →
--       --------------------------
--       Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

--   | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types)
--       {hFresh: x ∉ 𝒢.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧
--         y ∉ 𝒢.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names}
--       {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
--       Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
--       -------------------------------------
--       Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

--   | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types}
--       {hFresh : x ∉ Γ.names ∧ x ∉ Δ.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names}
--       {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
--       Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
--       ---------------------------------
--       Typing (Γ‚ Δ‚ x ∶ A ⨂ B) (x⟦y⟧․P)

--   | one {P : Proc} {x : PName} :
--       Typing ∅ P →
--       ----------------------
--       Typing (x ∶ 1) (x⟦⟧․P)

--   | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types}
--       {hFresh : x ∉ Γ.names ∧ y ∉ Γ.names}
--       {hneq : x ≠ y} :
--       Typing (Γ‚ y ∶ A‚ x ∶ B) P →
--       ------------------------------
--       Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩․P)

--   | bot {Γ : Env} {P : Proc} {x : PName} {hFresh : x ∉ Γ.names} :
--       Typing Γ P →
--       --------------------------
--       Typing (Γ‚ x ∶ ⊥) (x⸨⸩․P)

--   | oplus₁
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
--       Typing (Γ‚ x ∶ A) P →
--       ------------------------------
--       Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧․P)

--   | oplus₂
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
--       Typing (Γ‚ x ∶ B) P →
--       ------------------------------
--       Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧․P)

--   | amp
--       {Γ : Env} {P Q : Proc} {x : PName} {A B : Types} :
--       Typing (Γ‚ x ∶ A) P → Typing (Γ‚ x ∶ B) Q →
--       ---------------------------------------------
--       Typing (Γ‚ x ∶ A & B) (x․case{𝐋 : P, 𝐑 : Q})

--   | quest
--       {Γ : Env} {P : Proc} {x : PName} {A : Types} :
--       Typing (Γ‚ x ∶ A) P →
--       -----------------------------
--       Typing (Γ‚ x ∶ ??A) (x⟦USE⟧․P)

--   | bang
--       {Γ : Env} {P : Proc} {x : PName} {A : Types} :
--       Typing (Γ‚ x ∶ A) P → ?ₑΓ →
--       ------------------------------
--       Typing (Γ‚ x ∶ !!A) (!x․{P})

--   | w
--       {Γ : Env} {P : Proc} {x : PName} {A : Types} {hFrehs : x ∉ Γ.names} :
--       Typing Γ P →
--       -----------------------------
--       Typing (Γ‚ x ∶ ??A) (x⟦DISP⟧․P)

--   | c
--       {Γ : Env} {P : Proc} {x x' : PName} {A : Types}
--       {hneq : x ≠ x'} {hf : x ∉ Γ.names ∧ x' ∉ Γ.names} :
--       Typing (Γ‚ x ∶ ??A‚ x' ∶ ??A) P →
--       ---------------------------------
--       Typing (Γ‚ x ∶ ??A) (x⟦DUP⟧⸨x'⸩․P)

--   | exists_
--       {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar} :
--       Typing (Γ‚ x ∶ B{A // X}) P →
--       -----------------------------
--       Typing (Γ‚ x ∶ ∃X․B) (x⟦A⟧․P)

--   | forall_
--       {Γ : Env} {P : Proc} {x : PName} {B : Types} {X : TVar} :
--       Typing (Γ‚ x ∶ B) P → X ∉ ft(Γ)ₑ →
--       ---------------------------------
--       Typing (Γ‚ x ∶ ∀X․B) (x⸨X⸩․P)

--   | ax
--       {x y : PName} {A : Types} {hneq : x ≠ y} :
--       Typing (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₚ y)

-- notation:50 "⊢ " P " ∷ " T => Typing T P

-- -- Projection of a Judgement to its process
-- def proc {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : Proc := P

-- -- Projection of a Judgement to its environment
-- def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

-- lemma Typing.f_subset_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   P.f ⊆ 𝒢.names := by
--   induction h

--   case mix₀ => rfl

--   case mix ihP ihQ =>
--     simp
--     exact Finset.union_subset_union ihP ihQ

--   case one | bot | w =>
--     simp only [Proc.f, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton]
--     simp_all

--   case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.insert_subset
--     · simp
--     · exact ih

--   case amp ihP ihQ =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     · apply Finset.insert_subset
--       · simp
--       · exact Finset.union_subset ihP ihQ

--   case c ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.insert_subset
--     · simp
--     · intro a ha
--       simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
--       specialize ih ha.1
--       simp_all

--   case ax =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton, Finset.union_singleton]
--     simp [Finset.pair_comm]

--   case cut ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     rw [Finset.mem_sdiff] at ha
--     specialize ih ha.1
--     simp_all

--   case tensor ih | parr ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     simp at ⊢ ha ih
--     rcases ha with rfl | ⟨hP, hny⟩
--     · left ; rfl
--     · specialize ih hP ; simp at ih ; tauto

-- lemma Typing.names_subset_f {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   𝒢.names ⊆ P.f := by
--   induction h

--   case mix₀ => rfl

--   case mix ihP ihQ =>
--     simp
--     exact Finset.union_subset_union ihP ihQ

--   case one | bot | w =>
--     simp only [Proc.f, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton]
--     simp_all

--   case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.Subset.trans ih
--     apply Finset.subset_union_right

--   case amp ihP ihQ =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.Subset.trans ihP
--     exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right

--   case c ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.union_subset
--     · apply Finset.Subset.trans _ Finset.subset_union_right
--       apply Finset.subset_sdiff.mpr
--       constructor
--       · apply Finset.Subset.trans _ ih
--         rw [Finset.union_assoc]
--         exact Finset.subset_union_left
--       · simp_all
--     · exact Finset.subset_union_left

--   case ax =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton, Finset.union_singleton]
--     simp [Finset.pair_comm]

--   case cut hf _ _ _ ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     rw [Finset.mem_sdiff]
--     apply And.intro
--     · apply ih
--       simp_all
--     · simp_all
--       apply And.intro
--       all_goals
--         intro heq
--         rw [heq] at ha
--         exact hf.1 (by simp_all)

--   case tensor ih | parr ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     simp at ⊢ ha ih
--     rcases ha with rfl | h
--     · left ; rfl
--     · apply Or.inr
--       apply And.intro
--       · apply ih
--         simp_all
--       · intro heq
--         rw [heq] at h
--         simp_all

-- lemma Typing.f_eq_names {𝒢 : HyperEnv} {P : Proc} {h : ⊢ P ∷ 𝒢} :
--   P.f = 𝒢.names := by
--   exact Finset.Subset.antisymm (Typing.f_subset_names h) (Typing.names_subset_f h)

-- lemma Typing.not_mem_of_fresh_name {𝒢 : HyperEnv} {Γ : Env} {P : Proc} {x : PName}
--   {A : Types} (hf : x ∉ P.f) (hP : ⊢ P ∷ 𝒢) : Γ‚ x ∶ A ∉ 𝒢 := by
--   let Ex := Γ‚ x ∶ A
--   intro hc
--   have hx : x ∈ 𝒢.names := by
--     rw [HyperEnv.names, Finset.mem_biUnion]
--     use Ex
--     simp [hc, Ex, Env.names_distributes]
--   exact hf (Typing.names_subset_f hP hx)

-- theorem Typing.preserves_disjointness {P : Proc} {𝒢 : HyperEnv}
--   (h : ⊢ P ∷ 𝒢) : 𝒢.PairwiseDisjoint := by
--   induction h

--   case mix 𝒢 ℋ P Q hd _ _ ih𝒢 ihℋ =>
--     intro A hA B hB hneq
--     simp at hA hB
--     rcases hA with hA | hA <;> rcases hB with hB | hB
--     · exact ih𝒢 A hA B hB hneq
--     · apply Disjoint.mono
--         (HyperEnv.mem_implies_names_subset_self hA)
--         (HyperEnv.mem_implies_names_subset_self hB) hd
--     · apply Disjoint.mono
--         (HyperEnv.mem_implies_names_subset_self hA)
--         (HyperEnv.mem_implies_names_subset_self hB) hd.symm
--     · exact ihℋ A hA B hB hneq

--   case cut 𝒢' Γ Δ P x y A hf _ _ _ ih =>
--     let Ex := Γ‚ x ∶ A
--     let Ey := Δ‚ y ∶ Aᗮ
--     let E_new := Γ‚ Δ

--     have hpp : (𝒢' |ₕ {Ex} |ₕ {Ey}).PairwiseDisjoint := ih
--     intro E1 hE1 E2 hE2 hDiff
--     simp only [HyperEnv.merge, Finset.mem_union, Finset.mem_singleton] at hE1 hE2
--     rcases hE1 with hE1_𝒢 | rfl <;> rcases hE2 with hE2_𝒢 | rfl
--     · apply hpp E1
--       · simp [hE1_𝒢]
--       · simp [hE2_𝒢]
--       · exact hDiff

--     · simp only [Env.disjoint, Env.names_distributes]
--       apply Finset.disjoint_union_right.mpr

--       have hneq : E1 ≠ Ex ∧ E1 ≠ Ey := by
--         have hxy : x ∈ Ex.names ∧ y ∈ Ey.names:= by simp [Ex, Ey]
--         apply And.intro
--         · intro heq
--           rw [← heq] at hxy
--           · have hxG : x ∈ 𝒢'.names := Finset.mem_biUnion.mpr ⟨E1, hE1_𝒢, hxy.1⟩
--             exact hf.1 hxG
--         · intro heq
--           rw [← heq] at hxy
--           · have hG : y ∈ 𝒢'.names := Finset.mem_biUnion.mpr ⟨E1, hE1_𝒢, hxy.2⟩
--             exact hf.2.2.2.1 hG

--       have h_disj_E1_Ex : Disjoint E1.names Ex.names :=
--         hpp E1 (by simp [hE1_𝒢]) Ex (by simp [Ex]) hneq.1

--       have h_disj_E1_Ey : Disjoint E1.names Ey.names :=
--         hpp E1 (by simp [hE1_𝒢]) Ey (by simp [Ey]) hneq.2

--       apply And.intro
--       · apply Finset.disjoint_of_subset_right _ h_disj_E1_Ex
--         simp [Ex]
--       · apply Finset.disjoint_of_subset_right _ h_disj_E1_Ey
--         simp [Ey]

--     · simp only [Env.disjoint, Env.names_distributes]
--       apply Finset.disjoint_union_left.mpr

--       have hneq : E2 ≠ Ex ∧ E2 ≠ Ey := by
--         have hxy : x ∈ Ex.names ∧ y ∈ Ey.names:= by simp [Ex, Ey]
--         apply And.intro
--         · intro heq
--           rw [← heq] at hxy
--           · have hxG : x ∈ 𝒢'.names := Finset.mem_biUnion.mpr ⟨E2, hE2_𝒢, hxy.1⟩
--             exact hf.1 hxG
--         · intro heq
--           rw [← heq] at hxy
--           · have hG : y ∈ 𝒢'.names := Finset.mem_biUnion.mpr ⟨E2, hE2_𝒢, hxy.2⟩
--             exact hf.2.2.2.1 hG

--       have h_disj_E2_Ex : Disjoint E2.names Ex.names :=
--         hpp E2 (by simp [hE2_𝒢]) Ex (by simp [Ex]) hneq.1

--       have h_disj_E2_Ey : Disjoint E2.names Ey.names :=
--         hpp E2 (by simp [hE2_𝒢]) Ey (by simp [Ey]) hneq.2

--       apply And.intro
--       · apply Disjoint.symm
--         apply Finset.disjoint_of_subset_right _ h_disj_E2_Ex
--         simp [Ex]
--       · apply Disjoint.symm
--         apply Finset.disjoint_of_subset_right _ h_disj_E2_Ey
--         simp [Ey]

--     · contradiction

--   all_goals simp [HyperEnv.PairwiseDisjoint]





/- -------------------------------- Delete? -------------------------------- -/
-- throw in base?
-- lemma set_cancel {α : Type} [DecidableEq α] (S T : Finset α) (x : α)
--   (heq : S ∪ {x} = T ∪ {x}) (hnS : x ∉ S) (hnT : x ∉ T) : S = T := by
--   rw [← Finset.erase_insert hnS, ← Finset.erase_insert hnT]
--   simp only [Finset.insert_eq, Finset.union_comm, heq]

-- lemma HyperEnv.merge_cancel_right {𝒢 ℋ : HyperEnv} {Γ : Env}
--   (heq : 𝒢 |ₕ {Γ} = ℋ |ₕ {Γ}) (hn1 : Γ ∉ 𝒢) (hn2 : Γ ∉ ℋ) : 𝒢 = ℋ := by
--   apply set_cancel (x := Γ)
--   · simp only [HyperEnv.merge] at heq
--     exact heq
--   · exact hn1
--   · exact hn2
-----------------------------------------------------------------------------






-- lemma Typing.cut_inversion {𝒢 : HyperEnv} {P : Proc} {x y : PName}
--   (h : ⊢ 𝑣⸨x, y⸩ P ∷ 𝒢) : ∃ Γ Δ A 𝒢_ctx,
--     𝒢 = 𝒢_ctx |ₕ {Γ‚ Δ} ∧
--     x ∉ 𝒢_ctx.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧
--     y ∉ 𝒢_ctx.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names ∧
--     x ≠ y ∧ Γ.disjoint Δ ∧
--     ⊢ P ∷ 𝒢_ctx |ₕ {Γ‚ x ∶ A} |ₕ {Δ‚ y ∶ Aᗮ} := by
--   generalize hG : 𝒢 = 𝒢_in at h
--   cases h

--   case cut 𝒢' Γ' Δ' A' hd hf hneq 𝒟' =>
--     subst hG
--     simp at *
--     exists Γ', Δ', A', 𝒢'
--     refine ⟨rfl, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2,
--       hneq, hd, 𝒟'⟩



-- lemma Typing.cut_swap_dir {P : Proc} {x y a b : PName} {𝒢 : HyperEnv}
--   (hDisj : ({x, y} ∩ {a, b} : Finset PName) = ∅) (h : ⊢ 𝑣⸨x, y⸩ (𝑣⸨a, b⸩ P) ∷ 𝒢) :
--   ⊢ 𝑣⸨a, b⸩ (𝑣⸨x, y⸩ P) ∷ 𝒢 := by

--   obtain ⟨Γxy, Δxy, Axy, 𝒢xy, rfl,
--           hf_x𝒢, hf_xΓ, hf_xΔ,
--           hf_y𝒢, hf_yΓ, hf_yΔ,
--           hneq_xy, hd_xy, 𝒟'⟩ := Typing.cut_inversion h

--   obtain ⟨Γab, Δab, Aab, 𝒢ab, heq,
--           hf_a𝒢, hf_aΓ, hf_aΔ,
--           hf_b𝒢, hf_bΓ, hf_bΔ,
--           hneq_ab, hd_ab, 𝒟⟩ := Typing.cut_inversion 𝒟'

--   let Ex := Γxy‚ x ∶ Axy
--   let Ey := Δxy‚ y ∶ Axyᗮ
--   let Z  := Γab‚ Δab

--   have h_Ex : Ex ∈ 𝒢ab |ₕ {Z} := by rw [← heq] ; simp [HyperEnv.merge] ; right ; left ; rfl
--   have h_Ey : Ey ∈ 𝒢ab |ₕ {Z} := by rw [← heq] ; simp [HyperEnv.merge] ; left ; rfl

--   simp [HyperEnv.merge, Finset.mem_union, Finset.mem_singleton] at h_Ex h_Ey

--   sorry
--   -- Other approach define where Ex and Ey are instead.





--   -- have h_mem : (Γab‚ Δab) ∈ 𝒢xy |ₕ {Γxy‚ x ∶ Axy} |ₕ {Δxy‚ y ∶ Axyᗮ} := by
--   --   rw [heq] ; simp

--   -- simp at h_mem
--   -- rcases h_mem with hEy | hEx | h𝒢

--   -- -- CASE 1: Γab‚ Δab = Δxy‚ y ∶ Axyᗮ
--   -- · sorry

--   -- -- CASE 2: Γab‚ Δab = Γxy‚ x ∶ Axy
--   -- · sorry

--   -- -- CASE 3: Γab‚ Δab ∈ 𝒢xy
--   -- ·
--   --   let 𝒢rest := 𝒢xy.erase (Γab‚ Δab)
--   --   have h_decomp : 𝒢xy = 𝒢rest |ₕ {Γab‚ Δab} := by
--   --     rw [HyperEnv.merge_comm]
--   --     exact (Finset.insert_erase h𝒢).symm

--   --   rw [h_decomp, HyperEnv.merge_swap_last]
--   --   apply Typing.cut _ _ _ _ a b Aab
--   --   · -- Derivation need for outer cut to be valid
--   --     rw [HyperEnv.merge_assoc, HyperEnv.merge_swap_last, ← HyperEnv.merge_assoc]
--   --     apply Typing.cut _ _ _ _ x y Axy
--   --     ·

--   --       -- Derivation
--   --       convert 𝒟 using 1
--   --       rw [h_decomp] at heq
--   --       let Z := Γab‚ Δab

--   --       have h_isolation :
--   --         (𝒢ab |ₕ {Z}).erase Z =
--   --         ((𝒢rest |ₕ {Z}) |ₕ {Γxy‚ x ∶ Axy} |ₕ {Δxy‚ y ∶ Axyᗮ}).erase Z := by
--   --         rw [← heq]

--   --       simp at h_isolation
--   --       rw [Finset.erase_insert_of_ne] at h_isolation
--   --       · rw [Finset.erase_insert_of_ne] at h_isolation
--   --         · rw [Finset.erase_insert] at h_isolation
--   --           · have h_Z_not_in_Gab : Z ∉ 𝒢ab := by
--   --               intro h_contra
--   --               have h_a_in_Z : a ∈ Z.names := by sorry


--   --               have h_a_in_Gab : a ∈ 𝒢ab.names :=
--   --                 HyperEnv.mem_implies_names_subset_self h_contra h_a_in_Z

--   --               exact hf_a𝒢 h_a_in_Gab

--   --             rw [Finset.erase_eq_of_notMem h_Z_not_in_Gab] at h_isolation
--   --             rw [h_isolation]
--   --             simp only [Finset.insert_eq, HyperEnv.merge]
--   --             conv_rhs => rw [← Finset.union_assoc, Finset.union_assoc, Finset.union_assoc,
--   --               Finset.union_comm, Finset.union_comm ({Δxy‚ y ∶ Axyᗮ}) ({Γxy‚ x ∶ Axy}),
--   --               ← Finset.union_assoc, ← Finset.union_assoc]
--   --           · sorry
--   --         · sorry
--   --       · sorry




--   --     · split_ands
--   --       · sorry
--   --       · exact hf_xΓ
--   --       · exact hf_xΔ
--   --       · sorry
--   --       · exact hf_yΓ
--   --       · exact hf_yΔ
--   --     · exact hneq_xy
--   --     · exact hd_xy

--   --   · split_ands
--   --     · sorry
--   --     · exact hf_aΓ
--   --     · exact hf_aΔ
--   --     · sorry
--   --     · exact hf_bΓ
--   --     · exact hf_bΔ
--   --   · exact hneq_ab
--   --   · exact hd_ab

-- theorem Typing.respects_cong {𝒢 : HyperEnv} {P Q : Proc}
--   (hcong : P ≡ₚ Q) : (⊢ P ∷ 𝒢) ↔ (⊢ Q ∷ 𝒢) := by
--   induction hcong generalizing 𝒢

--   case refl => rfl

--   case symm ih => exact ih.symm

--   case trans h1 h2 ihP ihQ => exact Iff.trans ihP ihQ

--   case par_congr ih =>
--     apply Iff.intro <;>
--     · intro h
--       cases h
--       rename_i hd hP hQ
--       apply Typing.mix
--       · exact hd
--       · (try exact ih.mp hP) ; (try exact ih.mpr hP)
--       · exact hQ

--   case par_comm =>
--     apply Iff.intro
--     all_goals
--     · intro h
--       cases h
--       rename_i 𝒢' 𝒢'' hDisj hP hQ
--       rw [HyperEnv.merge_comm]
--       apply Typing.mix
--       · exact hDisj.symm
--       · exact hQ
--       · exact hP

--   case par_assoc =>
--     apply Iff.intro
--     · intro h
--       cases h
--       rename_i hPQ hR
--       cases hPQ
--       rename_i hP hQ
--       rw [HyperEnv.merge_assoc]
--       apply Typing.mix
--       · simp_all [HyperEnv.disjoint]
--       · exact hP
--       · apply Typing.mix
--         · simp_all [HyperEnv.disjoint]
--         · exact hQ
--         · exact hR
--     · intro h
--       cases h
--       rename_i hP hQR
--       cases hQR
--       rename_i hQ hR
--       rw [← HyperEnv.merge_assoc]
--       apply Typing.mix
--       · simp_all [HyperEnv.disjoint]
--       · apply Typing.mix
--         · simp_all [HyperEnv.disjoint]
--         · exact hP
--         · exact hQ
--       · exact hR

--   case par_zero =>
--     apply Iff.intro
--     · intro h
--       cases h
--       rename_i hDisj hP hQ
--       cases hQ
--       rw [HyperEnv.merge_unitR]
--       exact hP
--     · intro h
--       rw [← HyperEnv.merge_unitR 𝒢]
--       apply Typing.mix
--       · simp [HyperEnv.disjoint]
--       · exact h
--       · apply Typing.mix₀

--   case cut_congr ih =>
--     apply Iff.intro <;>
--     · intro h
--       cases h
--       rename_i hd hf hneq 𝒟
--       apply Typing.cut
--       · exact hf
--       · exact hneq
--       · exact hd
--       · (try exact ih.mp 𝒟) ; (try exact ih.mpr 𝒟)

--   case cut_scope hf1 =>
--     apply Iff.intro
--     · intro h
--       cases h
--       rename_i P Q x y 𝒢 ℋ hd1 hP hQ
--       cases hP
--       rename_i 𝒢' Γ Δ A hd2 hf hneq 𝒟
--       rw [HyperEnv.merge_comm, ← HyperEnv.merge_assoc]
--       apply Typing.cut
--       · simp only [HyperEnv.names_distributes, Finset.mem_union]
--         simp
--         repeat' apply And.intro
--         · intro hxℋ
--           have hxQ := Typing.names_subset_f hQ hxℋ
--           exact hf1.1 hxQ
--         · exact hf.1
--         · exact hf.2.1
--         · exact hf.2.2.1
--         · intro hyℋ
--           have hyQ := Typing.names_subset_f hQ hyℋ
--           exact hf1.2 hyQ
--         · exact hf.2.2.2.1
--         · exact hf.2.2.2.2.1
--         · exact hf.2.2.2.2.2
--       · exact hneq
--       · exact hd2
--       · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc, HyperEnv.merge_comm,
--             ← HyperEnv.merge_assoc]
--         apply Typing.mix
--         · simp [HyperEnv.disjoint, HyperEnv.names]
--           repeat' apply And.intro
--           · intro Γ hΓℋ hxΓ
--             have hxℋ : x ∈ ℋ.names := Finset.mem_biUnion.mpr ⟨Γ, hΓℋ, hxΓ⟩
--             have hxQ := Typing.names_subset_f hQ hxℋ
--             exact hf1.1 hxQ
--           · intro Γ hΓℋ hyΓ
--             have hyℋ : y ∈ ℋ.names := Finset.mem_biUnion.mpr ⟨Γ, hΓℋ, hyΓ⟩
--             have hyQ := Typing.names_subset_f hQ hyℋ
--             exact hf1.2 hyQ
--           · apply Finset.disjoint_of_subset_left _ hd1
--             simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--               Env.names_distributes, ← Finset.union_assoc, Finset.subset_union_right]
--           · apply Finset.disjoint_of_subset_left _ hd1
--             simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--               Env.names_distributes, ← Finset.union_assoc, Finset.union_comm Γ.names Δ.names,
--               Finset.subset_union_right]
--           · apply Finset.disjoint_of_subset_left _ hd1
--             simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--               Env.names_distributes]
--             simp only [HyperEnv.names, Finset.subset_union_left]
--         · exact 𝒟
--         · exact hQ
--     · intro h
--       rename_i x y
--       cases h
--       rename_i P' Q' 𝒢 Γ Δ A hd1 hf hneq 𝒟
--       generalize heq : (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) = 𝒥
--       rw [heq] at 𝒟
--       cases 𝒟
--       rename_i 𝒢' ℋ' hd2 hP hQ
--       · let Ex := Γ‚ x ∶ A
--         let Ey := Δ‚ y ∶ Aᗮ
--         let Ctx := {Ex} |ₕ {Ey}

--         have hTotal : Ex ∈ (𝒢 |ₕ Ex |ₕ Ey) ∧ Ey ∈ (𝒢 |ₕ Ex |ₕ Ey) := by simp

--         rw [heq] at hTotal
--         simp [HyperEnv.merge, Finset.mem_union] at hTotal

--         have hninℋ' : Ex ∉ ℋ' ∧ Ey ∉ ℋ':=
--           ⟨Typing.not_mem_of_fresh_name hf1.1 hQ,
--           Typing.not_mem_of_fresh_name hf1.2 hQ⟩

--         have hin𝒢' : Ex ∈ 𝒢' ∧ Ey ∈ 𝒢' :=
--           ⟨Or.resolve_right hTotal.1 hninℋ'.1,
--           Or.resolve_right hTotal.2 hninℋ'.2⟩

--         let 𝒢'_base := 𝒢' \ {Ex, Ey}
--         have h𝒢' : 𝒢' = 𝒢'_base |ₕ {Ex} |ₕ {Ey} := by
--           simp only [𝒢'_base, HyperEnv.merge]
--           rw [Finset.union_assoc, Finset.union_comm ({Ex} : HyperEnv) ({Ey} : HyperEnv),
--             Finset.union_singleton]
--           symm
--           apply Finset.sdiff_union_of_subset
--           simp [Finset.insert_subset_iff]
--           exact ⟨hin𝒢'.1, hin𝒢'.2⟩

--         have h𝒢 : 𝒢 = 𝒢'_base |ₕ ℋ' := by
--           simp only [h𝒢'] at heq
--           rw [HyperEnv.merge_comm _ ℋ', ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc] at heq
--           apply Finset.ext
--           intro e
--           simp only [HyperEnv.merge, Finset.mem_union]
--           simp only [HyperEnv.merge] at heq
--           constructor
--           · intro he𝒢
--             have hin : e ∈ 𝒢'_base ∪ ℋ' ∪ Ctx := by
--               simp only [Ctx, HyperEnv.merge, ← Finset.union_assoc,
--                 Finset.union_comm _ ℋ']
--               rw [← heq]
--               rw [Finset.union_assoc]
--               apply Finset.mem_union_left
--               exact he𝒢
--             simp only [Ctx, HyperEnv.merge, Finset.mem_union] at hin
--             rcases hin with h1 | h2
--             · exact h1
--             · rcases h2
--               · rename_i h3
--                 exfalso
--                 apply hf.1
--                 rw [HyperEnv.names, Finset.mem_biUnion]
--                 rw [Finset.mem_singleton] at h3
--                 rw [h3] at he𝒢
--                 use Ex, he𝒢
--                 simp [Ex, Env.names_distributes]
--               · rename_i h4
--                 exfalso
--                 apply hf.2.2.2.1
--                 rw [HyperEnv.names, Finset.mem_biUnion]
--                 rw [Finset.mem_singleton] at h4
--                 rw [h4] at he𝒢
--                 use Ey, he𝒢
--                 simp [Ey, Env.names_distributes]
--           · intro hRHS
--             have hin : e ∈ ℋ' ∪ 𝒢'_base ∪ {Ex} ∪ {Ey} := by
--               simp only [Finset.mem_union, Finset.mem_singleton]
--               rcases hRHS with h1 | h2
--               · left ; left ; right ; exact h1
--               · left ; left ; left ; exact h2
--             rw [← heq] at hin
--             simp only [Finset.mem_union, Finset.mem_singleton] at hin
--             rcases hin with h𝒢 | rfl | rfl
--             · rcases h𝒢 with h1 | rfl
--               · exact h1
--               · exfalso
--                 rcases hRHS with h1 | h2
--                 · simp [𝒢'_base, Ex] at h1
--                 · exact hninℋ'.1 h2
--             · exfalso
--               rcases hRHS with h1 | h2
--               · simp [𝒢'_base, Ey] at h1
--               · exact hninℋ'.2 h2

--         have hd' : (𝒢'_base |ₕ {Γ‚ Δ}).disjoint ℋ' := by
--           simp only [HyperEnv.disjoint] at *
--           simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
--             Env.names_distributes, Finset.disjoint_union_left]
--           split_ands
--           · apply Finset.disjoint_of_subset_left _ hd2
--             rw [h𝒢']
--             simp only [HyperEnv.names_distributes, Finset.union_assoc,
--               Finset.subset_union_left]
--           · apply Finset.disjoint_of_subset_left _ hd2
--             have hΓEx : Γ.names ⊆ Ex.names := by simp [Ex]
--             have hEx𝒢' : Ex.names ⊆ 𝒢'.names :=
--               HyperEnv.mem_implies_names_subset_self hin𝒢'.1
--             exact Finset.Subset.trans hΓEx hEx𝒢'
--           · apply Finset.disjoint_of_subset_left _ hd2
--             have hΔEy : Δ.names ⊆ Ey.names := by simp [Ey]
--             have hEy𝒢' : Ey.names ⊆ 𝒢'.names :=
--               HyperEnv.mem_implies_names_subset_self hin𝒢'.2
--             exact Finset.Subset.trans hΔEy hEy𝒢'

--         have hf' : x ∉ 𝒢'_base.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧ y ∉ 𝒢'_base.names
--           ∧ y ∉ Γ.names ∧ y ∉ Δ.names := by
--           rcases hf with ⟨hx𝒢, hxΓ, hxΔ, hy𝒢, hyΓ, hyΔ⟩
--           refine ⟨?_, hxΓ, hxΔ, ?_, hyΓ, hyΔ⟩
--           · intro h_contra
--             apply hx𝒢
--             rw [h𝒢]
--             simp only [HyperEnv.names_distributes, Finset.mem_union]
--             left
--             exact h_contra
--           · intro h_contra
--             apply hy𝒢
--             rw [h𝒢]
--             simp only [HyperEnv.names_distributes, Finset.mem_union]
--             left
--             exact h_contra

--         rw [h𝒢, HyperEnv.merge_comm, ← HyperEnv.merge_assoc, HyperEnv.merge_comm _ 𝒢'_base]
--         apply Typing.mix
--         · exact hd'
--         · apply Typing.cut _ _ _ _ _ _ A
--           · rw [h𝒢'] at hP
--             simp only [Ex, Ey] at hP
--             exact hP
--           · exact hf'
--           · exact hneq
--           · exact hd1
--         · exact hQ

--   case cut_swap P' x y a b hDisj =>
--     apply Iff.intro
--     · apply Typing.cut_swap_dir hDisj
--     · intro h
--       rw [Finset.inter_comm] at hDisj
--       apply Typing.cut_swap_dir hDisj h





-- FIXME: add openTVar (Exists and forall)?

-- FIXME: add types and name substitution

inductive Typing : Nat → Proc → HyperEnv → Prop where
  ------ Additional Structural and Exchange Rules ------

  | exchange_env {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {n : Nat} :
      Typing n P (Γ :: 𝒢) → Γ ~ Δ →
      -----------------------------
      Typing n P (Δ :: 𝒢)

  | exchange_hyper {𝒢 ℋ : HyperEnv} {P : Proc} {n : Nat} :
      Typing n P 𝒢 → 𝒢 ~ ℋ →
      -----------------------
      Typing n P ℋ

  ----------------- Actual Typing Rules -----------------

  | mix₀ {n : Nat} :
      Typing n 𝟘 ∅

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {hD : 𝒢.disjoint ℋ} {n : Nat} :
      Typing n P 𝒢 → Typing n Q ℋ →
      ------------------------------
      Typing n (P |ₚ Q) (𝒢 |ₕ ℋ)

  | one {P : Proc} {x : FPName} {n : Nat} :
      Typing n P ∅ →
      ---------------------------
      Typing n (#x⟦⟧․P) [[x ∶ 1]]

  | bot {Γ : Env} {P : Proc} {x : FPName} {hF : x ∉ Γ.names} {n : Nat} :
      Typing n P [Γ] →
      ------------------------------
      Typing n (#x⸨⸩․P) [x ∶ ⊥ :: Γ]

  | cut {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {A : Types} (L : Finset FPName) {n : Nat} :
      (∀ x y, x ∉ L → y ∉ L → x ≠ y →
      Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])) →
      ----------------------------------------------------------
      Typing n (𝑣⸨#,#⸩P) (𝒢 |ₕ [Γ‚ Δ])

  | tensor {Γ Δ : Env} {P : Proc} {x : FPName} {B A : Types}
      {hF : x ∉ Γ.names ∧ x ∉ Δ.names} (L : Finset FPName) {n : Nat} :
      (∀ y, y ∉ L → Typing n (P⸨#y⸩) ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) →
      ---------------------------------------------------------------
      Typing n (#x⟦#N⟧․P) [x ∶ A ⨂ B :: Γ‚ Δ]

  | parr {Γ : Env} {P : Proc} {x : FPName} {A B : Types}
      {hF : x ∉ Γ.names} (L : Finset FPName) {n : Nat} :
      (∀ y, y ∉ L → Typing n (P⸨#y⸩) [x ∶ B :: y ∶ A :: Γ]) →
      -------------------------------------------------------
      Typing n (#x⸨#N⸩․P) [x ∶ A ⅋ B :: Γ]

  | oplus₁
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      lcType n B →
      Typing n P [x ∶ A :: Γ] →
      -----------------------------------
      Typing n (#x⟦𝐋⟧․P) [x ∶ A ⊕ B :: Γ]

  | oplus₂
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      lcType n A →
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
      ---------------------------------
      Typing n (!#x․{P}) [x ∶ !!A :: Γ]

  | w
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {hF : x ∉ Γ.names} {n : Nat} :
      lcType n A → Typing n P [Γ] →
      -----------------------------------
      Typing n (#x⟦DISP⟧․P) [x ∶ ??A :: Γ]

  | c
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} (L : Finset FPName) {n : Nat} :
      (∀ x', x' ∉ L →
      Typing n P⸨#x'⸩ [x ∶ ??A :: x' ∶ ??A :: Γ]) →
      --------------------------------------------
      Typing n (#x⟦DUP⟧⸨#N⸩․P) [x ∶ ??A :: Γ]

  | exists_
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      lcType n A →
      Typing n P [x ∶ B{A // #T} :: Γ] →
      ----------------------------------
      Typing n (#x⟦A⟧․P) [x ∶ ∃․B :: Γ]

  | forall_
      {Γ : Env} {P : Proc} {x : FPName} {B : Types} {n : Nat} :
      Typing (n + 1) P [x ∶ B :: Γ⁺ᵗ] →
      ----------------------------------
      Typing n (#x⸨#T⸩․P) [x ∶ ∀․B :: Γ]

  | ax
      {x y : FPName} {A : Types} {hneq : x ≠ y} {n : Nat} :
      lcType n A →
      Typing n (#x ⟷ₚ #y) [x ∶ Aᗮ :: [y ∶ A]]

notation:45 n " ⊢ " P " ∷ " 𝒢 => Typing n P 𝒢

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

  case mix hD _ _ _ ih𝒢 ihℋ =>
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

  case c L _ _ ih | tensor L _ _ ih | parr L _ _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    constructor
    · intro a ha
      simp_all [HyperEnv.PairwiseDisjoint, Env.names]
    · simp

  case ax hneq _ _ =>
    constructor <;> simp_all

  case cut L _ _ ih =>
    obtain ⟨u, v, hu, hv, hneq⟩ := exists_two_fresh L
    specialize ih u v hu hv hneq

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
    rw [HyperEnv.PairwiseDisjoint, ← List.Perm.pairwise_iff _ hP]
    · exact ih
    · intro x y hD
      simp at hD ⊢
      apply Disjoint.symm
      exact hD

lemma Typing_preserves_lc {𝒢 : HyperEnv} {P : Proc} {n : Nat} :
  (n ⊢ P ∷ 𝒢) → ∀ Γ ∈ 𝒢, lcEnv n Γ := by
  intro hT E hE𝒢
  induction hT generalizing E

  case mix₀ => simp_all

  case mix =>
    simp at hE𝒢
    cases hE𝒢 <;> simp_all

  case one | bot | quest | bang | amp | oplus₁ | oplus₂ | w | ax =>
    simp_all [lcEnv_cons, lcType_dual.mp]
    simp_all [lcEnv, lcType]

  case exists_ Γ _ x A B n hlc _ ih =>
    simp at hE𝒢
    subst hE𝒢
    have h : lcEnv n ((x, B{A // #T}) :: Γ) := ih ((x, B{A // #T}) :: Γ) (by simp)
    rw [lcEnv_cons] at h ⊢
    exact ⟨(lcType_subst_inv_0 hlc).mp h.1, by simp_all⟩

  case forall_ Γ _ x B n _ ih =>
    simp at hE𝒢
    subst hE𝒢
    have h : lcEnv (n + 1) ((x, B) :: Γ⁺ᵗ) := ih ((x, B) :: Γ⁺ᵗ) (by simp)
    simp_all [lcEnv_cons]
    constructor
    · simp [lcType, h.1]
    · exact lcEnv_shift_inv_0.mp h.2

  case cut Γ Δ _ A L n _  ih =>
    obtain ⟨u, v, hu, hv, hneq⟩ := exists_two_fresh L
    specialize ih u v hu hv hneq
    simp at hE𝒢
    cases hE𝒢 with
    | inl => simp_all
    | inr hin =>
      subst hin
      have hΓ : lcEnv n ((u, A) :: Γ) := ih ((u, A) :: Γ) (by simp)
      have hΔ : lcEnv n ((v, Aᗮ) :: Δ) := ih ((v, Aᗮ) :: Δ) (by simp)
      rw [lcEnv_cons] at hΓ hΔ
      exact lcEnv_append.mpr ⟨hΓ.2, hΔ.2⟩

  case tensor L _ _ ih | parr L _ _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [lcEnv_cons]
    simp_all [lcType, lcEnv_append]

  case c L _ _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [lcEnv_cons]

  case exchange_env hP ih =>
    simp_all
    cases hE𝒢 with
    | inl => simp_all [(lcEnv_perm hP).mp]
    | inr => simp_all

  case exchange_hyper hP _ =>
    simp_all [List.Perm.mem_iff hP]


/- FIXME:
  Need weakening to allow for processes with varying depth to be mixed when using De Bruijn indices.
-/
-- FIXME: Need shift defined on Proc
-- lemma weakening_preserves_typing {n : Nat} {P : Proc} {Γ : Env} :
--   Typing n P Γ → ∀ (k : Nat), Typing (n + k) (P.shift k) (Γ.shift k) := by sorry

-- FIXME: Typing_preserves_proc_congr

-- FIXME: Fix ProcStep and EnvStep
-- FIXME: Name and Type substitution
-- FIXME: Subject reduction


-- lemma Types.subst_shift_comm {A B : Types} {k : Nat} :
--   (B{A // #T}) ↑ k = (B ↑ 1, k){A ↑ k // #T} := by sorry






@[simp] lemma Env.shift_empty {d c : Nat} :
  ([] : Env) ↑ᵗ d, c = ([] : Env) := by
  simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shift_singleton {d c : Nat} {x : FPName} {A : Types} :
  [x ∶ A] ↑ᵗ d, c = [x ∶ A ↑ᵗ d, c] := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shift_cons {d k : Nat} {Γ : Env} {x : FPName} {A : Types} :
  (x ∶ A :: Γ) ↑ᵗ d, k = x ∶ A ↑ᵗ d, k :: Γ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shift_append {d k : Nat} {Γ Δ : Env} :
  (Γ ++ Δ) ↑ᵗ d, k = Γ ↑ᵗ d, k ++ Δ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, Env.shiftTypes]

@[simp] lemma Env.shift_preserves_names {d c : Nat} {Γ : Env} :
  (Γ ↑ᵗ d, c).names = Γ.names := by
  simp [HasShiftTypes.shift, Env.shiftTypes, Env.names]
  rfl

@[simp] lemma Env.shift_preserves_disjoint {d c : Nat} {Γ Δ : Env} :
  Γ.disjoint Δ → (Γ ↑ᵗ d, c).disjoint (Δ ↑ᵗ d, c) := by simp


@[simp] lemma HyperEnv.shift_empty {d c : Nat} :
  ([] : HyperEnv) ↑ᵗ d, c = ([] : HyperEnv) := by
  simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shift_singleton {d c : Nat} {Γ : Env} :
  [Γ] ↑ᵗ d, c = [Γ ↑ᵗ d, c] := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shift_cons {d k : Nat} {𝒢 : HyperEnv} {Γ : Env} :
  (Γ :: 𝒢) ↑ᵗ d, k = Γ ↑ᵗ d, k :: 𝒢 ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes, Env.shiftTypes]

@[simp] lemma HyperEnv.shift_append {d k : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢 ++ ℋ) ↑ᵗ d, k = 𝒢 ↑ᵗ d, k ++ ℋ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.names_cons {Γ : Env} {𝒢 : HyperEnv} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.shift_preserves_names {d c : Nat} {𝒢 : HyperEnv} :
  (𝒢 ↑ᵗ d, c).names = 𝒢.names := by
  induction 𝒢 <;> simp_all

@[simp] lemma HyperEnv.shift_preserves_disjoint {d c : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢.disjoint ℋ) → ((𝒢 ↑ᵗ d, c).disjoint (ℋ ↑ᵗ d, c)) := by simp




@[simp] lemma Proc.shift_nil {d c : Nat} :
  𝟘 ↑ᶜ d, c = 𝟘 := by
  simp [HasShiftNames.shift, Proc.shiftNames]

@[simp] lemma Proc.shift_ax {d c : Nat} {x y : FPName} :
  (#x⟷ₚ#y) ↑ᶜ d, c = (#x⟷ₚ#y) := by
  simp [HasShiftNames.shift, Proc.shiftNames]

@[simp] lemma Proc.shift_par {d c : Nat} {P Q : Proc} :
  (P |ₚ Q) ↑ᶜ d, c = P ↑ᶜ d, c |ₚ Q ↑ᶜ d, c := by
  simp [HasShiftNames.shift, Proc.shiftNames]

@[simp] lemma Proc.shift_one {d c : Nat} {P : Proc} {x : FPName} :
  (#x⟦⟧․P) ↑ᶜ d, c = #x⟦⟧․(P ↑ᶜ d, c) := by
  simp [HasShiftNames.shift, Proc.shiftNames]

@[simp] lemma Proc.shift_bot {d c : Nat} {P : Proc} {x : FPName} :
  (#x⸨⸩․P) ↑ᶜ d, c = #x⸨⸩․(P ↑ᶜ d, c) := by
  simp [HasShiftNames.shift, Proc.shiftNames]

@[simp] lemma Proc.shift_cut {d c : Nat} {P : Proc} :
  (𝑣⸨#,#⸩ P) ↑ᶜ d, c = 𝑣⸨#,#⸩ (P ↑ᶜ (d + 2), c) := by
  simp [HasShiftNames.shift, Proc.shiftNames]




-- FIXME:
-- @[simp] lemma Proc.shift_open_comm {d c : Nat} {P : Proc} {x y : FPName} :
--   (P⸨#x, #y⸩) ↑ᶜ d, c = (P ↑ᶜ d, c) ⸨#x, #y⸩ := by
--   simp [Proc.openCut]






-- FIXME:
lemma Typing_weakening {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  Typing n P 𝒢 → ∀ k, Typing (n + k) (P ↑ᵗ k) (𝒢 ↑ᵗ k) := by
  intro h
  induction h
  all_goals (
    try simp_all
    intro k
  )

  case mix₀ n' => exact Typing.mix₀

  case mix hD _ _ ihP ihQ =>
    apply Typing.mix
    · simp ; exact hD
    · exact ihP k
    · exact ihQ k

  case ax hneq hlc =>
    rw [Types.shift_dual_comm]
    exact Typing.ax
      (hneq := hneq)
      ((lcType_shift_c_inv (c := k) (d := 0)).mpr hlc)

  case one ih =>
    exact Typing.one (ih k)

  case bot hF _ _ ih =>
    exact Typing.bot (hF := by simp [hF]) (ih k)

  case cut A L _ _ ih =>

    apply Typing.cut L (A := A ↑ᵗ k)
    intros x y hx hy hneq
    specialize ih x y hx hy hneq
    rw [← Types.shift_dual_comm]
    specialize ih k
    simp

    sorry

  all_goals sorry













-- lemma Typing.f_subset_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   P.f ⊆ 𝒢.names := by
--   induction h

--   case mix₀ => rfl

--   case mix ihP ihQ =>
--     simp
--     exact Finset.union_subset_union ihP ihQ

--   case one | bot | w =>
--     simp only [Proc.f, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton]
--     simp_all

--   case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.insert_subset
--     · simp
--     · exact ih

--   case amp ihP ihQ =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     · apply Finset.insert_subset
--       · simp
--       · exact Finset.union_subset ihP ihQ

--   case c ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.insert_subset
--     · simp
--     · intro a ha
--       simp only [Finset.mem_sdiff, Finset.mem_singleton] at ha
--       specialize ih ha.1
--       simp_all

--   case ax =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton, Finset.union_singleton]
--     simp [Finset.pair_comm]

--   case cut ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     rw [Finset.mem_sdiff] at ha
--     specialize ih ha.1
--     simp_all

--   case tensor ih | parr ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     simp at ⊢ ha ih
--     rcases ha with rfl | ⟨hP, hny⟩
--     · left ; rfl
--     · specialize ih hP ; simp at ih ; tauto

-- lemma Typing.names_subset_f {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
--   𝒢.names ⊆ P.f := by
--   induction h

--   case mix₀ => rfl

--   case mix ihP ihQ =>
--     simp
--     exact Finset.union_subset_union ihP ihQ

--   case one | bot | w =>
--     simp only [Proc.f, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton]
--     simp_all

--   case oplus₁ ih | oplus₂ ih | quest ih | bang ih | exists_ ih | forall_ ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.Subset.trans ih
--     apply Finset.subset_union_right

--   case amp ihP ihQ =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.Subset.trans ihP
--     exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right

--   case c ih =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton] at *
--     apply Finset.union_subset
--     · apply Finset.Subset.trans _ Finset.subset_union_right
--       apply Finset.subset_sdiff.mpr
--       constructor
--       · apply Finset.Subset.trans _ ih
--         rw [Finset.union_assoc]
--         exact Finset.subset_union_left
--       · simp_all
--     · exact Finset.subset_union_left

--   case ax =>
--     simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
--       Env.names_singleton, Finset.union_singleton]
--     simp [Finset.pair_comm]

--   case cut hf _ _ _ ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     rw [Finset.mem_sdiff]
--     apply And.intro
--     · apply ih
--       simp_all
--     · simp_all
--       apply And.intro
--       all_goals
--         intro heq
--         rw [heq] at ha
--         exact hf.1 (by simp_all)

--   case tensor ih | parr ih =>
--     simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
--       Env.names_distributes, Env.names_singleton] at *
--     intro a ha
--     simp at ⊢ ha ih
--     rcases ha with rfl | h
--     · left ; rfl
--     · apply Or.inr
--       apply And.intro
--       · apply ih
--         simp_all
--       · intro heq
--         rw [heq] at h
--         simp_all

-- lemma Typing.f_eq_names {𝒢 : HyperEnv} {P : Proc} {h : ⊢ P ∷ 𝒢} :
--   P.f = 𝒢.names := by
--   exact Finset.Subset.antisymm (Typing.f_subset_names h) (Typing.names_subset_f h)
