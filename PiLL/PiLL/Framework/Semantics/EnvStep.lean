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

  | par₁
      {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl} :
      EnvStep 𝒢 l 𝒢' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢' |ₕ ℋ)

  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {l : Lbl} :
      EnvStep ℋ l ℋ' →
      -----------------------------
      EnvStep (𝒢 |ₕ ℋ) l (𝒢 |ₕ ℋ')

  | syn
      {𝒢 𝒢' ℋ ℋ': HyperEnv} {l l' : Act} :
      EnvStep 𝒢 l 𝒢' → EnvStep ℋ l' ℋ' → (l |ₗ l').WF →
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

  | res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : FPName} {A B : Types} {l : Lbl} :
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
      {Γ : Env} {x : FPName} {A B : Types} {X : TVar} :
      EnvStep [x ∶ ∃․B :: Γ] (x⟦A⟧) [x ∶ B{A // 0} :: Γ]

  | input
      {Γ : Env} {x : FPName} {A B : Types} {X : TVar} :
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


@[simp] lemma Env.names_nil :
  Env.names [] = ∅ := by simp [Env.names]

@[simp] lemma Env.names_singleton {x : FPName} {A : Types} :
  Env.names [(x ∶ A)] = {x} := by simp [Env.names]

@[simp] lemma Env.names_distributes {Γ : Env} {x : FPName} {A : Types} :
  Env.names ((x ∶ A) :: Γ) = {x} ∪ Γ.names := by simp [Env.names]

@[simp] lemma Env.names_merge {Γ Δ : Env} :
  Env.names (Γ‚ Δ) = Γ.names ∪ Δ.names := by simp [Env.names]




@[simp] lemma HyperEnv.names_nil :
  HyperEnv.names [] = ∅ := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_singleton {Γ : Env} :
  HyperEnv.names [Γ] = Γ.names := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_merge {𝒢 ℋ : HyperEnv} :
  HyperEnv.names (𝒢 |ₕ ℋ) = 𝒢.names ∪ ℋ.names := by
  induction 𝒢 with
  | nil => simp
  | cons Γ 𝒢' ih =>
    simp only [HyperEnv.names_distributes]
    simp [HyperEnv.names] at ⊢ ih
    rw [ih]

lemma EnvStep.preserves_disjoint {𝒢 𝒢' ℋ : HyperEnv} {l : Lbl}
  (hES : 𝒢 -[l]->ₑ 𝒢') (hD : 𝒢.names ∩ ℋ.names = ∅) (hFl : l.i ∩ ℋ.names = ∅) :
  𝒢'.names ∩ ℋ.names = ∅ := by
  induction hES

  case one => simp [HyperEnv.names, Env.names]

  case bot =>
    rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
    simp only [HyperEnv.names, Env.names] at hD ⊢
    simp only [List.foldr, List.map, List.toFinset_cons, Finset.union_empty] at hD ⊢
    exact (Finset.disjoint_insert_left.mp hD).right

  case tensor =>
    rw [← Finset.disjoint_iff_inter_eq_empty] at hD hFl ⊢
    rw [Finset.disjoint_left] at hD hFl ⊢
    intro n hn
    simp only [HyperEnv.names_merge, Finset.mem_union] at hn
    simp [Finset.mem_insert] at hn
    rcases hn with h1 | h2
    · rcases h1 with rfl | _ <;> simp_all
    · rcases h2 with rfl | _ <;> simp_all

  case parr B _ =>
    rw [← Finset.disjoint_iff_inter_eq_empty] at hD hFl ⊢
    rw [Finset.disjoint_left] at hD hFl ⊢
    intro n hn
    simp only [HyperEnv.names_distributes, Finset.mem_union] at hn
    simp [Finset.mem_insert] at hn
    rcases hn with h1 | h2
    · simp_all
    · rcases h2 with rfl | h
      · simp_all
      · simp at hD
        cases h with
        | intro T hin =>
          exact hD.2 n T hin

  case par₁ 𝒢 𝒢' _ l _ ih =>
    rw [← Finset.disjoint_iff_inter_eq_empty] at hD hFl ⊢
    rw [Finset.disjoint_left] at hD hFl ⊢
    intro n hn
    simp only [HyperEnv.names_merge, Finset.mem_union] at hn
    cases hn
    case inl h =>
      have hD : 𝒢.names ∩ ℋ.names = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
        intro a ha
        apply hD
        rw [HyperEnv.names_merge, Finset.mem_union]
        left
        exact ha

      have hDl : l.i ∩ ℋ.names = ∅ := by
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
        exact hFl

      have hD' : 𝒢'.names ∩ ℋ.names = ∅ := ih hD hDl
      rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left] at hD'
      exact hD' h

    case inr hin =>
      apply hD
      simp
      apply Or.inr (hin)

  case par₂ _ 𝒢 𝒢' l _ ih =>
    rw [← Finset.disjoint_iff_inter_eq_empty] at hD hFl ⊢
    rw [Finset.disjoint_left] at hD hFl ⊢
    intro n hn
    simp only [HyperEnv.names_merge, Finset.mem_union] at hn
    cases hn



  all_goals sorry
