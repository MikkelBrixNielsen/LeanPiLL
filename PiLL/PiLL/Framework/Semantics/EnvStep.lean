import PiLL.Framework.Model.Judgement
import PiLL.Framework.Semantics.Labels

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  ------------------ Actual Step Rules ------------------

  | one
      {x : FPName} :
      EnvStep [[x ∶ 1]] (x⟦⟧) ∅

  | tensor
      {Γ Δ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ]) :
      EnvStep [x ∶ A ⨂ B :: Γ‚ Δ] (x⟦x'⟧) ([x' ∶ A :: Γ] |ₕ [x ∶ B :: Δ])

  | bot
      {Γ : Env} {x : FPName} :
      EnvStep [x ∶ ⊥ :: Γ] (x⸨⸩) [Γ]

  | parr
      {Γ : Env} {x x' : FPName} {A B : Types}
      (hF : x' ∉ HyperEnv.names [x ∶ A ⅋ B :: Γ]) :
      EnvStep [x ∶ A ⅋ B :: Γ] (x⸨x'⸩) [x' ∶ A :: x ∶ B :: Γ]

  -- NOTE: added disjointness contraints to par₁, par₂ and syn to mimic ProcStep contraint
  -- as not to have to do mutual induction on EnvStep and ProcStep to show Linearity.
  -- Remark 3.6 from the paper [1] (main.pdf)
  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStep 𝒢 l 𝒢' →
      l.i ∩ ℋ.names = ∅ → -- Added to mimic ProcStep
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStep ℋ l ℋ' →
      l.i ∩ 𝒢.names = ∅ → -- Added to mimic ProcStep
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStep 𝒢 l 𝒢' → EnvStep ℋ l' ℋ' →
      (l |ₗ l').i ∩ (𝒢 |ₕ ℋ).names = ∅ → (l |ₗ l').WF → -- Added to mimic ProcStep
      --------------------------------------------------
      EnvStep (𝒢 |ₕ ℋ) (l |ₗ l') (𝒢' |ₕ ℋ')

  | one_bot
      {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
      EnvStep (𝒢 |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) (x⟦⟧ |ₗ y⸨⸩) (𝒢 |ₕ [Γ]) →
      ---------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ]) (τ) (𝒢 |ₕ [Γ])

  | tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {x x' y y': FPName} {A B : Types} :
      EnvStep
        (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])
        (x⟦x'⟧ |ₗ y⸨y'⸩)
        (𝒢 |ₕ [x' ∶ A :: Γ] |ₕ [x' ∶ A :: Δ] |ₕ [y ∶ Bᗮ :: y' ∶ Aᗮ :: Ξ]) →
      ------------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ‚ Δ‚ Ξ]) (τ) (𝒢 |ₕ [Γ‚ Δ‚ Ξ])

  -- NOTE: hneq : x ≠ y, is only here for convenience to prove EnvStep.preserves_linearity as
  -- a stand alone property. Given The Typing relating a ProcStep and EnvStep, this could be
  -- extracted from the fact that a Typing preserves linearity of Envs.
  -- The same is true for hFlx : x ∉ l.i ∪ l.f and hFly : y ∉ l.i ∪ l.f due to linearity, if
  -- x and y persist across the step then no duplicates guarantee that its the same x and y
  -- as such they could not have been mentioned in the label.
  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A : Types} {l : Lbl}
      (hFx : x ∉ (𝒢 |ₕ [Γ‚ Δ]).names) (hFy : y ∉ (𝒢 |ₕ [Γ‚ Δ]).names)
      (hFx' : x ∉ (𝒢' |ₕ [Γ'‚ Δ']).names) (hFy' : y ∉ (𝒢' |ₕ [Γ'‚ Δ']).names)
      (hFlx : x ∉ l.i ∪ l.f) (hFly : y ∉ l.i ∪ l.f) (hneq : x ≠ y) :
      EnvStep (𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]) (l) (𝒢' |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ']) →
      -------------------------------------------------------------------------------------
      EnvStep (𝒢 |ₕ [Γ‚ Δ]) l (𝒢' |ₕ [Γ'‚ Δ'])

  | selectL
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A ⊕ B :: Γ] (x⟦𝐋⟧) [x ∶ A :: Γ]

  | ampL
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A & B :: Γ] (x⸨𝐋⸩) [x ∶ A :: Γ]

  | selectR
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A ⊕ B :: Γ] (x⟦𝐑⟧) [x ∶ B :: Γ]

  | ampR
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ A & B :: Γ] (x⸨𝐑⸩) [x ∶ B :: Γ]

  | link₁
      {x y : FPName} {A : Types} :
      EnvStep [x ∶ Aᗮ :: [y ∶ A]] (x ⟷ₗ y) ∅

  | use₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A :: Γ] (x⟦USE⟧) [x ∶ A :: Γ]

  | use₂
      {Γ : Env} {x : FPName} {A : Types} :
      ?ₑΓ →
      -------------------------------------------
      EnvStep [x ∶ !!A :: Γ] (x⸨USE⸩) [x ∶ A :: Γ]

  | disp₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A :: Γ] (x⟦DISP⟧) [x ∶ ⊥ :: Γ]

  | disp₂
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ !!A :: Γ] (x⸨DISP⸩) [x ∶ 1 :: Γ]

  | dup₁
      {Γ : Env} {x : FPName} {A : Types} :
      EnvStep [x ∶ ??A:: Γ] (x⟦DUP⟧) [x ∶ ??A ⅋ ??A :: Γ]

  | dup₂
      {Γ : Env} {x : FPName} {A : Types} :
      ?ₑΓ →
      ---------------------------------------------------
      EnvStep [x ∶ !!A :: Γ] (x⸨DUP⸩) [x ∶ !!A ⨂ !!A :: Γ]

  | output
      {Γ : Env} {x : FPName} {A B : Types} :
      EnvStep [x ∶ ∃․B :: Γ] (x⟦A⟧) [x ∶ B{A // 0} :: Γ]

  | input
      {Γ : Env} {x : FPName} {A B : Types} :
      A.lc 0 →
      EnvStep [x ∶ ∀․B :: Γ] (x⸨A⸩) [x ∶ B{A // 0} :: Γ]

------- Additional Structural / Exchange Rules -------

    | perm {𝒢 𝒢' ℋ ℋ' : HyperEnv} {l : Lbl} :
      𝒢 ~ ℋ → EnvStep 𝒢 l 𝒢' → 𝒢' ~ ℋ' →
      ------------------------------------
      EnvStep ℋ l ℋ'

notation:50 P " -[" l "]->ₑ " P' => EnvStep P l P'

theorem EnvStep.preserves_WF (Γ Γ' : HyperEnv) (l : Lbl) :
  EnvStep Γ l Γ' → l.WF := by
  intro h
  induction h <;> simp_all [Lbl.WF]

inductive MEST : (𝒢 : HyperEnv) → Lbls → (𝒢' : HyperEnv) → Prop where
  | refl
    {𝒢 : HyperEnv} :
    -------------
    MEST 𝒢 (ε) 𝒢

  | stepR {l : Lbl} {ls : Lbls} {𝒢 𝒢'' 𝒢' : HyperEnv} :
    (MEST 𝒢 ls 𝒢'') → (𝒢'' -[l]->ₑ 𝒢') →
    ------------------------------------
          MEST 𝒢 (ls ∷ₗ l) 𝒢'

notation:50 𝒢 " -[" ls "]->>ₑ " 𝒢' => MEST 𝒢 ls 𝒢'

@[simp] lemma EnvStep.names_subset {𝒢 𝒢' : HyperEnv} {l : Lbl} :
  (𝒢 -[l]->ₑ 𝒢') → 𝒢'.names ⊆ 𝒢.names ∪ l.i := by
  intro h
  induction h
  case tensor | parr =>
    simp ; rw [Finset.insert_comm]

  case par₁ | par₂ =>
    grind [HyperEnv.names_merge]

  case syn =>
    grind [HyperEnv.names_merge, Lbl.i]

  case res 𝒢 𝒢' Γ Γ' Δ Δ' x y _ l hFx hFy hFx' hFy' _ _ _ _ ih =>
    simp_all only [HyperEnv.names_merge, HyperEnv.names_singleton, Env.names_merge,
      Env.names_distributes, Lbl.i, Finset.mem_union]
    intro n hn

    simp only [Finset.mem_union] at hn

    have hnx : n ≠ x := by rintro rfl ; exact hFx' hn
    have hny : n ≠ y := by rintro rfl ; exact hFy' hn

    have hinLHS : n ∈ 𝒢'.names ∪ ({x} ∪ Γ'.names) ∪ ({y} ∪ Δ'.names) := by
      simp only [Finset.mem_union, Finset.mem_singleton]
      rcases hn with h𝒢 | hΓ | hΔ <;> grind

    have hPrev:= ih hinLHS
    simp only [Finset.mem_union, Finset.mem_singleton] at ⊢ hPrev
    rcases hPrev with ((h𝒢 | (hx | hΓ)) | (hy | hΔ)) | hM <;> grind

  case perm hP _ hP' ih =>
    have heq := HyperEnv.names_eq_of_perm hP
    have heq' := HyperEnv.names_eq_of_perm hP'
    rw [← heq, ← heq']
    exact ih

  all_goals simp

lemma EnvStep.preserves_disjoint {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl}
  (hES : 𝒢 -[l]->ₑ 𝒢') (hD : 𝒢.disjoint ℋ) (hFl : Disjoint l.i ℋ.names) :
  𝒢'.disjoint ℋ := by
  exact Disjoint.mono_left (EnvStep.names_subset hES) (Finset.disjoint_union_left.mpr ⟨hD, hFl⟩)

-- NOTE: There have been placed additional constraints on par₁, par₂, res and syn in EnvStep to
-- make this a standalone property, and getting it to type check. Ideally, these would be removed
-- and mutual induction would be done on ProcStep and EnvStep related by a valid Typing instead.
-- The added contraints are either provided by constraints on ProcStep or can be extracted from
-- The Typing relation using the `Typing_preserves_XXX` lemmas.
lemma EnvStep.preserves_Linearity {𝒢 𝒢' : HyperEnv} {l : Lbl}
  (hlin : 𝒢.Linearity) (hES : 𝒢 -[l]->ₑ 𝒢') : 𝒢'.Linearity := by
  induction hES

  case one | link₁ => simp

  case tensor hF =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons, Env.Nodup_merge_iff] at ⊢ hlin hF
    split_ands
    · exact hF.2.1
    · exact hlin.2.1
    · exact hlin.1.2
    · exact hlin.2.2.1
    · simp_all [← ne_eq, HyperEnv.PairwiseDisjoint]
      exact hF.1.symm

  case bot =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hlin
    exact hlin.2

  case parr hF =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hlin hF
    constructor
    · exact hF
    · exact hlin

  case par₁ hES hDl ih =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin
    constructor
    · exact ih hlin𝒢
    · constructor
      · exact hlinℋ
      · intro E1 hE1 E2 hE2
        have hsub𝒢'𝒢:= EnvStep.names_subset hES
        have hsubE1 :=
          Finset.Subset.trans (HyperEnv.subset_names_of_mem hE1) hsub𝒢'𝒢
        apply Finset.disjoint_of_subset_left hsubE1
        rw [Finset.disjoint_union_left]
        constructor
        · rw [HyperEnv.disjoint_names_left]
          intro a ha
          exact hD a ha E2 hE2
        · rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
          exact Finset.disjoint_of_subset_right (HyperEnv.subset_names_of_mem hE2) hDl

  case par₂ hES hDl ih =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin
    constructor
    · exact hlin𝒢
    · constructor
      · exact ih hlinℋ
      · intro E1 hE1 E2 hE2
        have hsubℋ'ℋ := EnvStep.names_subset hES
        have hsubE2 :=
          Finset.Subset.trans (HyperEnv.subset_names_of_mem hE2) hsubℋ'ℋ
        apply Finset.disjoint_of_subset_right hsubE2
        rw [Finset.disjoint_union_right]
        constructor
        · rw [HyperEnv.disjoint_names_right]
          intro a ha
          exact hD E1 hE1 a ha
        · rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
          exact Finset.disjoint_of_subset_left (HyperEnv.subset_names_of_mem hE1) hDl.symm

  case syn hES𝒢 hESℋ hDl lwf ihP ihQ =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin

    constructor
    · exact ihP hlin𝒢
    · constructor
      · exact ihQ hlinℋ
      · intro E1 hE1 E2 hE2
        rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
        rw [Lbl.WF, ← Finset.disjoint_iff_inter_eq_empty] at lwf
        simp only [HyperEnv.merge, HyperEnv.names_merge, Lbl.i,
          Finset.disjoint_union_left, Finset.disjoint_union_right] at hDl
        obtain ⟨⟨hDl1, hDl2⟩, ⟨hDl3, hDl4⟩⟩ := hDl

        have hsubE1 := Finset.Subset.trans
          (HyperEnv.subset_names_of_mem hE1)
          (EnvStep.names_subset hES𝒢)

        have hsubE2:= Finset.Subset.trans
          (HyperEnv.subset_names_of_mem hE2)
          (EnvStep.names_subset hESℋ)

        apply Finset.disjoint_of_subset_left hsubE1
        apply Finset.disjoint_of_subset_right hsubE2

        rw [Finset.disjoint_union_left, Lbl.i, Lbl.i]
        constructor
        · rw [Finset.disjoint_union_right]
          constructor
          · rw [HyperEnv.disjoint_names_left]
            intro E3 hE3
            rw [HyperEnv.disjoint_names_right]
            intro E4 hE4
            exact hD E3 hE3 E4 hE4
          · exact hDl2.symm
        · rw [Finset.disjoint_union_right]
          constructor
          · exact hDl3
          · exact lwf

  case one_bot | tensor_parr => exact hlin

  case res 𝒢 𝒢' Γ Γ' Δ Δ' x y A l hFx hFy hFx' hFy' _ _ hneq hES𝒢 ih =>
    simp [Env.Nodup_merge_iff] at hlin ⊢ hFx hFx' hFy hFy'
    obtain ⟨hlin𝒢, ⟨hndΓ, ⟨hndΔ, hDΓΔ⟩⟩, hD⟩ := hlin
    have hlin_inner : (𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]).Linearity := by
      simp
      constructor
      · exact hlin𝒢
      · constructor
        · change HyperEnv.Linearity ([x ∶ Aᗮ :: Γ] |ₕ  [y ∶ A :: Δ])
          simp only [HyperEnv.Linearity_merge]
          constructor
          · simp [Env.Nodup_cons]
            constructor
            · exact hFx.2.1
            · exact hndΓ
          · constructor
            · simp [Env.Nodup_cons]
              constructor
              · exact hFy.2.2
              · exact hndΔ
            · intro a ha b hb
              simp at ha hb
              simp [ha, hb]
              exact ⟨⟨hneq.symm, hFy.2.1⟩, ⟨hFx.2.2, hDΓΔ⟩⟩
        · intro a ha
          obtain ⟨hDΓ, hDΔ⟩ := hD a ha
          refine ⟨⟨?_, hDΓ⟩, ⟨?_, hDΔ⟩⟩
          · intro T hxT
            apply hFx.1
            rw [HyperEnv.mem_pair_fst_in_names]
            use T, a
          · intro T hyT
            apply hFy.1
            rw [HyperEnv.mem_pair_fst_in_names]
            use T, a

    have hlin_outer:= ih hlin_inner

    simp at hlin_outer
    obtain ⟨hlin𝒢', hlin_xy, hD'⟩ := hlin_outer
    change HyperEnv.Linearity ([x ∶ Aᗮ :: Γ'] |ₕ  [y ∶ A :: Δ']) at hlin_xy
    simp only [HyperEnv.Linearity_merge, HyperEnv.Linearity_singleton, Env.Nodup_cons] at hlin_xy
    obtain ⟨hlin_xΓ', hlin_yΔ', hD_xΓ'yΔ'⟩ := hlin_xy
    simp at hD_xΓ'yΔ'

    split_ands
    · exact hlin𝒢'.1
    · exact hlin𝒢'.2
    · exact hlin_xΓ'.2
    · exact hlin_yΔ'.2
    · exact hD_xΓ'yΔ'.2.2
    · intro a ha
      have ⟨⟨_, haΓ'⟩, _, haΔ'⟩:= hD' a ha
      constructor
      · exact haΓ'
      · exact haΔ'

  case selectL | selectR | ampL | ampR | use₁ | use₂ | disp₁ | disp₂
    | dup₁ | dup₂ | output | input =>
    simp [Env.Nodup_cons] at hlin ⊢
    exact hlin

  case perm hP _ hP' ih =>
    exact hP'.preserves_Linearity (ih (hP.symm.preserves_Linearity hlin))
