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
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A B : Types} {l : Lbl}
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

  case res 𝒢 𝒢' Γ Γ' Δ Δ' x y _ _ l hFx hFy hFx' hFy' _ _ _ _ ih =>
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
