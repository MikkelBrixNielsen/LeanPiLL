import PiLL.Model.HyperEnvironment.Basic
import PiLL.Model.Environment.Lemmas

lemma HyperEnv.subset_names_of_mem {Γ : Env} {G : HyperEnv} (h : Γ ∈ G) :
  Γ.names ⊆ G.names := by
  induction G with
  | nil => contradiction
  | cons Δ 𝒢' ih =>
    simp only [names, List.mem_cons, List.foldr_cons] at *
    cases h with
    | inl => simp_all
    | inr hΓ =>
      apply Finset.Subset.trans (ih hΓ)
      apply Finset.subset_union_right

@[simp] lemma HyperEnv.substNames_singleton {Γ : Env} {x y : FPName} :
  ([Γ] : HyperEnv){y // x} = [Γ{y // x}] := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_distributes {𝒢 : HyperEnv} {Γ : Env} {x y : FPName} :
  (Γ :: 𝒢){y // x} = Γ{y // x} :: 𝒢{y // x} := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_merge {𝒢 ℋ : HyperEnv} {x y : FPName} :
  (𝒢 |ₕ ℋ){y // x} = 𝒢{y // x} |ₕ ℋ{y // x} := by
  simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.substNames_nil {x y : FPName} :
  ([] : HyperEnv){y // x} = [] := by simp [HasSubst.subst, HyperEnv.substNames]

@[simp] lemma HyperEnv.shiftTypes_empty {d c : Nat} :
  ([] : HyperEnv) ↑ᵗ d, c = ([] : HyperEnv) := by
  simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_singleton {d c : Nat} {Γ : Env} :
  [Γ] ↑ᵗ d, c = [Γ ↑ᵗ d, c] := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_cons {d k : Nat} {𝒢 : HyperEnv} {Γ : Env} :
  (Γ :: 𝒢) ↑ᵗ d, k = Γ ↑ᵗ d, k :: 𝒢 ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes, Env.shiftTypes]

@[simp] lemma HyperEnv.shiftTypes_append {d k : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢 ++ ℋ) ↑ᵗ d, k = 𝒢 ↑ᵗ d, k ++ ℋ ↑ᵗ d, k := by
    simp [HasShiftTypes.shift, HyperEnv.shiftTypes]

@[simp] lemma HyperEnv.names_cons {Γ : Env} {𝒢 : HyperEnv} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.shiftTypes_preserves_names {d c : Nat} {𝒢 : HyperEnv} :
  (𝒢 ↑ᵗ d, c).names = 𝒢.names := by
  induction 𝒢 <;> simp_all

@[simp] lemma HyperEnv.shiftTypes_preserves_disjoint {d c : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢.disjoint ℋ) → ((𝒢 ↑ᵗ d, c).disjoint (ℋ ↑ᵗ d, c)) := by simp

@[simp] lemma HyperEnv.shiftTypes_preserves_perm {d c : Nat} {𝒢 ℋ : HyperEnv} :
  (𝒢 ~ ℋ) → (𝒢 ↑ᵗ d, c ~ ℋ ↑ᵗ d, c) := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.shiftTypes_preserves_perm hPE) ih
  | swap Γ Δ 𝒢 => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

@[simp] lemma HyperEnv.substNames_self {𝒢 : HyperEnv} {x : FPName} :
  𝒢{x // x} = 𝒢 := by induction 𝒢 generalizing x <;> simp_all

@[simp] lemma HyperEnv.substNames_of_not_mem {𝒢 : HyperEnv} {x y : FPName} :
  x ∉ 𝒢.names → (𝒢{y // x} = 𝒢) := by
  induction 𝒢
  case nil => simp only [substNames_nil, implies_true]
  case cons E HE ih =>
    simp only [names_cons, Finset.mem_union, not_or, substNames_distributes,
      List.cons.injEq, and_imp] at ⊢ ih
    intros hxE hxHE
    constructor
    · exact Env.substNames_of_not_mem hxE
    · exact ih hxHE

lemma HyperEnv.substNames_preserves_perm {𝒢 ℋ : HyperEnv} {x y : FPName} :
  𝒢 ~ ℋ → 𝒢{y // x} ~ ℋ{y // x} := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.substNames_preserves_perm hPE) ih
  | swap => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

lemma HyperEnv.mem_pair_fst_in_names {𝒢 : HyperEnv} {x : FPName} :
   x ∈ 𝒢.names ↔ ∃ A Γ, (x, A) ∈ Γ ∧ Γ ∈ 𝒢 := by
   induction 𝒢
   case nil => simp_all [HyperEnv.names]
   case cons hd tl ih =>
    constructor
    case mp =>
      intro h
      simp [Env.mem_pair_fst_in_names_iff] at h
      cases h
      case inl hL =>
        cases hL
        case intro T hin =>
          use T, hd
          exact ⟨hin, by simp⟩
      case inr hR =>
        have := ih.mp hR
        simp_all
        obtain ⟨T, Γ, hinΓ, hinℋ⟩ := this
        use T, Γ
        exact ⟨hinΓ, by apply Or.inr ; exact hinℋ⟩
    case mpr =>
      intro h
      obtain ⟨T, Γ, hinΓ, hOr⟩ := h
      cases hOr
      case head =>
        simp_all [Env.mem_pair_fst_in_names_iff]
        apply Or.inl
        use T
      case tail hMem =>
        simp_all
        apply Or.inr
        use T, Γ
        constructor
        · exact hinΓ
        · apply hMem

lemma HyperEnv.mem_names_substNames {𝒢 : HyperEnv} {x y z : FPName} :
  z ∈ (𝒢{y // x}).names ↔ (z = y ∧ x ∈ 𝒢.names) ∨ (z ∈ 𝒢.names ∧ z ≠ x) := by
  induction 𝒢 <;> simp_all [Env.mem_pair_fst_in_names_iff, HasSubst.subst, HyperEnv.substNames]
  case nil => simp [HyperEnv.names]
  case cons hd tl ih =>
    constructor
    case mp => grind [Env.substNames, Env.mem_pair_fst_in_names_iff]
    case mpr =>
      intro h
      cases h with
      | inl h' =>
        cases h'
        case inl.intro heq hin =>
          cases hin with
          | inl hin =>
            cases hin
            case inl.intro T hin =>
              apply Or.inl
              use T
              subst heq
              apply Env.mem_substNames hin
          | inr hin => grind
      | inr h' =>
        cases h'
        case inr.intro h1 hneq =>
          cases h1
          case inl hin =>
            cases hin
            case intro T hin =>
              apply Or.inl
              use T
              exact Env.mem_substNames_of_ne hin hneq (y := y)
          case inr => grind

lemma HyperEnv.substNames_preserves_disjoint {𝒢 ℋ : HyperEnv} {x y : FPName}
  (hD : 𝒢.disjoint ℋ) (huniq : ∀ Γ ∈ 𝒢 |ₕ ℋ, ∀ A, (y, A) ∈ Γ → y = x) :
  𝒢{y // x}.disjoint ℋ{y // x} := by
  simp_all only [HyperEnv.disjoint]
  grind [HyperEnv.mem_names_substNames, Finset.disjoint_left, HyperEnv.mem_pair_fst_in_names]

@[simp] lemma HyperEnv.substTypes_singleton {Γ : Env} {A : Types} {k : Nat} :
  ([Γ] : HyperEnv){A // k} = [Γ{A // k}] := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_distributes {𝒢 : HyperEnv} {Γ : Env} {A : Types} {k : Nat} :
  (Γ :: 𝒢){A // k} = Γ{A // k} :: 𝒢{A // k} := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_merge {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  (𝒢 |ₕ ℋ){A // k} =  𝒢{A // k} |ₕ ℋ{A // k} := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_nil {A : Types} {k : Nat} :
  ([] : HyperEnv){A // k} = [] := by simp [HasSubst.subst, HyperEnv.substTypes]

@[simp] lemma HyperEnv.substTypes_preserves_names {𝒢 : HyperEnv} {A : Types} {k : Nat} :
  𝒢{A // k}.names = 𝒢.names := by
  induction 𝒢 <;> simp_all

@[simp] lemma HyperEnv.substTypes_preserves_disjoint {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  𝒢.disjoint ℋ → 𝒢{A // k}.disjoint ℋ{A // k} := by simp

@[simp] lemma HyperEnv.substTypes_preserves_perm {𝒢 ℋ : HyperEnv} {A : Types} {k : Nat} :
  (𝒢 ~ ℋ) → (𝒢{A // k} ~ ℋ{A // k}) := by
  intro h
  induction h with
  | nil => exact HyperEnv.Perm.nil
  | cons hPE _ ih => exact HyperEnv.Perm.cons (Env.substTypes_preserves_perm hPE) ih
  | swap => exact HyperEnv.Perm.swap ..
  | trans _ _ ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

-- 𝒢{A // k}⁺ᵗ = 𝒢⁺ᵗ{A⁺ᵗ // k + 1}
@[simp] lemma HyperEnv.shiftTypes_subst_comm {𝒢 : HyperEnv} {A : Types} {k : Nat} :
  (𝒢.substTypes A k).shiftTypes 0 1 = (𝒢.shiftTypes 0 1).substTypes (A.shift 0 1) (k + 1) := by
  induction 𝒢 <;>
    simp [HyperEnv.substTypes, HyperEnv.shiftTypes, Env.substTypes,
      Env.shiftTypes, Types.shift_0_subst_comm]

lemma HyperEnv.Perm_mem {𝒢 ℋ : HyperEnv} {Γ : Env} (h : 𝒢 ~ ℋ) (hΓ : Γ ∈ ℋ) :
  ∃ Γ', Γ' ∈ 𝒢 ∧ Γ' ~ Γ := by
  induction h generalizing Γ with
  | nil => contradiction
  | cons hHead _ ih =>
    simp only [List.mem_cons] at hΓ
    rcases hΓ with rfl | hTail
    · simp_all
    · obtain ⟨Γ', hMem, hP⟩ := ih hTail
      use Γ'
      constructor
      · exact List.mem_cons_of_mem _ hMem
      · exact hP
  | swap Γ Δ 𝒢 =>
    simp only [List.mem_cons] at hΓ
    rcases hΓ with rfl | rfl | hTail
    · use Γ
      rw [List.mem_cons]
      constructor
      · apply Or.inr
        rw [List.mem_cons]
        exact Or.inl (rfl)
      · simp [HasPerm.perm]
    · use Γ
      constructor
      · rw [List.mem_cons]
        exact Or.inl (rfl)
      · exact List.Perm.refl Γ
    · use Γ
      constructor
      · rw [List.mem_cons]
        apply Or.inr
        rw [List.mem_cons]
        exact Or.inr (hTail)
      · exact List.Perm.refl Γ
  | trans _ _ ih1 ih2 =>
    obtain ⟨Ξ, hΞ, hPΞ⟩ := ih2 hΓ
    obtain ⟨Ξ', hΞ', hPΞ'⟩ := ih1 hΞ
    use Ξ'
    constructor
    · exact hΞ'
    · exact List.Perm.trans hPΞ' hPΞ

lemma HyperEnv.Perm_PairwiseDisjoint_iff {𝒢 ℋ : HyperEnv} :
  (𝒢 ~ ℋ) → (List.Pairwise Env.disjoint 𝒢 ↔ List.Pairwise Env.disjoint ℋ) := by
  intro h
  induction h with
  | nil => simp
  | cons hPE hPH ih =>
    rename_i Γ Δ 𝒢' ℋ'
    constructor
    · intro h
      rw [List.pairwise_cons] at ⊢ h
      obtain ⟨h1, h2⟩ := h
      constructor
      · intros Ξ hΞ
        obtain ⟨Ξ', hMemΞ', hPΞ'⟩ := HyperEnv.Perm_mem hPH hΞ
        have hDΔΞ' := (Env.perm_disjoint hPE).mp (h1 Ξ' hMemΞ')
        exact ((Env.perm_disjoint (Ξ := Δ) hPΞ').mp hDΔΞ'.symm).symm
      · exact ih.mp h2
    · intro h
      rw [List.pairwise_cons] at ⊢ h
      obtain ⟨h1, h2⟩ := h
      constructor
      · intros Ξ hΞ
        obtain ⟨Ξ', hMemΞ', hPΞ'⟩ := HyperEnv.Perm_mem hPH.symm hΞ
        have hDΓΞ' := (Env.perm_disjoint hPE).mpr (h1 Ξ' hMemΞ')
        exact ((Env.perm_disjoint (Ξ := Γ) hPΞ').mp hDΓΞ'.symm).symm
      · apply ih.mpr h2
  | swap =>
    rename_i Γ Δ 𝒢'
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    rw [Env.disjoint_symm]
    tauto
  | trans _ _ ih1 ih2 => exact Iff.trans ih1 ih2

@[simp] lemma HyperEnv.names_nil :
  HyperEnv.names [] = ∅ := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_singleton (Γ : Env) :
  HyperEnv.names [Γ] = Γ.names := by
  simp [HyperEnv.names, Env.names, List.foldr]

@[simp] lemma HyperEnv.names_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names, Env.names]

@[simp] lemma HyperEnv.names_merge (𝒢 ℋ : HyperEnv) :
  (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  induction 𝒢
  case nil => simp [HyperEnv.names]
  case cons _ _ ih => simp ; rw [ih]

lemma HyperEnv.names_eq_of_perm {𝒢 ℋ : HyperEnv} (h : 𝒢 ~ ℋ) :
  𝒢.names = ℋ.names := by
  induction h with
  | nil => simp
  | cons hPE _ ih => simp ; rw [Env.names_eq_of_perm hPE, ih]
  | swap Γ Δ => simp ; rw [← Finset.union_assoc, Finset.union_comm Γ.names _, Finset.union_assoc]
  | trans _ _ ih1 ih2 => apply Eq.trans ih1 ih2

@[simp, refl] lemma HyperEnv.Perm_refl {𝒢 : HyperEnv} :
  𝒢 ~ 𝒢 := by simp [HasPerm.perm]

@[simp] lemma HyperEnv.Nodup_nil :
  HyperEnv.Nodup [] := by simp [HyperEnv.Nodup]

@[simp] lemma HyperEnv.Nodup_singleton {Γ : Env} :
  HyperEnv.Nodup [Γ] = Env.Nodup Γ := by simp [HyperEnv.Nodup]

lemma HyperEnv.Nodup_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.Nodup (Γ :: 𝒢) ↔ HyperEnv.Nodup [Γ] ∧ HyperEnv.Nodup  𝒢 := by
  simp [HyperEnv.Nodup]

@[simp] lemma HyperEnv.Nodup_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).Nodup ↔ (𝒢.Nodup ∧ ℋ.Nodup) := by
  simp [HyperEnv.merge, HyperEnv.Nodup, Env.Nodup]
  constructor
  · intro h
    constructor
    · intro Γ hin ; exact h Γ (Or.inl hin)
    · intro Γ hin ; exact h Γ (Or.inr hin)
  · intro h1 Γ hin
    cases hin with
    | inl hin => exact h1.1 Γ hin
    | inr hin => exact h1.2 Γ hin

@[simp] lemma HyperEnv.Nodup_cons_iff {Γ : Env} {x : FPName} {A : Types} (hF : x ∉ Γ.names) :
  HyperEnv.Nodup [x ∶ A :: Γ] ↔ (HyperEnv.Nodup [[x ∶ A]] ∧ HyperEnv.Nodup [Γ]) := by
  simp_all [HyperEnv.Nodup, Env.Nodup_cons]

@[simp] lemma HyperEnv.Nodup_cons {Γ : Env} {x : FPName} {A : Types} :
  HyperEnv.Nodup [x ∶ A :: Γ] → (HyperEnv.Nodup [[x ∶ A]] ∧ HyperEnv.Nodup [Γ]) := by
  simp_all [HyperEnv.Nodup, Env.Nodup_cons]

lemma HyperEnv.Nodup_cons_perm_iff {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.Nodup (Γ :: 𝒢) ↔ HyperEnv.Nodup (Δ :: 𝒢) := by
  constructor
  · intros h E hE
    simp only [List.mem_cons] at hE
    rcases hE with rfl | h_in_G
    · have hNodupΓ : Env.Nodup Γ := by
        apply h
        simp
      exact (Env.Perm.nodup_iff hP).mp hNodupΓ
    · apply h
      simp [h_in_G]
  · intros h E hE
    simp only [List.mem_cons] at hE
    rcases hE with rfl | h_in_G
    · have hNodupΔ : Env.Nodup Δ := by
        apply h
        simp
      exact (Env.Perm.nodup_iff hP).mpr hNodupΔ
    · apply h
      simp [h_in_G]

lemma HyperEnv.Nodup_perm {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  HyperEnv.Nodup 𝒢 → HyperEnv.Nodup ℋ := by
  intro h
  simp_all [Nodup]
  intro E hE
  obtain ⟨Γ, hin, hPE⟩ := (HyperEnv.Perm_mem hP hE)
  exact Env.Nodup_perm hPE (h Γ hin)

lemma HyperEnv.Nodup_perm_iff {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  HyperEnv.Nodup 𝒢 ↔ HyperEnv.Nodup ℋ := by
  constructor
  · intro h ; exact HyperEnv.Nodup_perm hP h
  · intro h ; exact HyperEnv.Nodup_perm hP.symm h

@[simp] lemma HyperEnv.PairwiseDisjoint_nil :
  HyperEnv.PairwiseDisjoint [] := by simp [HyperEnv.PairwiseDisjoint]

@[simp] lemma HyperEnv.PairwiseDisjoint_singleton {Γ : Env} :
  HyperEnv.PairwiseDisjoint [Γ] := by simp [HyperEnv.PairwiseDisjoint]

@[simp] lemma HyperEnv.PairwiseDisjoint_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).PairwiseDisjoint ↔ (𝒢.PairwiseDisjoint ∧ ℋ.PairwiseDisjoint
    ∧ ∀ a ∈ 𝒢, ∀ b ∈ ℋ, Disjoint a.names b.names) := by
  simp [HyperEnv.merge, HyperEnv.PairwiseDisjoint]
  constructor
  · intro h
    simp [List.pairwise_append] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  · intro h
    rw [List.pairwise_append]
    exact ⟨h.1, h.2.1, h.2.2⟩

@[simp] lemma HyperEnv.PairwiseDisjoint_cons {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) → (HyperEnv.PairwiseDisjoint [Γ] ∧
  HyperEnv.PairwiseDisjoint 𝒢) := by
  simp [HyperEnv.PairwiseDisjoint]

lemma HyperEnv.PairwiseDisjoint_cons_perm {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) → HyperEnv.PairwiseDisjoint (Δ :: 𝒢) := by
  intro h
  simp [HyperEnv.PairwiseDisjoint] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro a ha
    have hDΓ := h1 a ha
    have hPNames := List.Perm.map Prod.fst hP
    have hNamesEq : Γ.names = Δ.names := by
      ext x
      simp [Env.names]
      constructor
      · intro h
        obtain ⟨A, hinΓ⟩ := h
        use A
        exact (List.Perm.mem_iff (a := (x, A)) hP).mp hinΓ
      · intro h
        obtain ⟨A, hinΔ⟩ := h
        use A
        exact (List.Perm.mem_iff (a := (x, A)) hP.symm).mp hinΔ
    rw [← hNamesEq]
    exact hDΓ
  · exact h2

lemma HyperEnv.PairwiseDisjoint_cons_perm_iff {𝒢 : HyperEnv} {Γ Δ : Env} (hP : Γ ~ Δ) :
  HyperEnv.PairwiseDisjoint (Γ :: 𝒢) ↔ HyperEnv.PairwiseDisjoint (Δ :: 𝒢) := by
  constructor
  · intro h ; exact HyperEnv.PairwiseDisjoint_cons_perm hP h
  · intro h ; exact HyperEnv.PairwiseDisjoint_cons_perm hP.symm h

lemma HyperEnv.mem_of_disjoint {𝒢 ℋ : HyperEnv} (hD : 𝒢.disjoint ℋ) :
  ∀ Γ ∈ 𝒢, ∀ Δ ∈ ℋ, Γ.disjoint Δ := by
  intro Γ hΓ Δ hΔ
  apply Disjoint.mono _ _ hD
  · exact HyperEnv.subset_names_of_mem hΓ
  · exact HyperEnv.subset_names_of_mem hΔ

@[simp] lemma HyperEnv.swap_two_inner {x y : FPName} {A B : Types} :
  [[x ∶ A, y ∶ B]] ~ [[y ∶ B, x ∶ A]] := by
  exact HyperEnv.Perm.cons Env.Perm.swap_two HyperEnv.Perm.nil

@[simp] lemma HyperEnv.disjoint_split {𝒢 ℋ : HyperEnv} (hD : (𝒢 |ₕ ℋ).PairwiseDisjoint) :
  𝒢.disjoint ℋ := by
  rw [HyperEnv.disjoint, Finset.disjoint_left]
  rw [HyperEnv.PairwiseDisjoint, HyperEnv.merge, List.pairwise_append] at hD
  intro n hin𝒢 hinℋ
  rw [HyperEnv.mem_pair_fst_in_names] at hin𝒢 hinℋ
  obtain ⟨T1, Γ, hinΓ, hΓ𝒢⟩ := hin𝒢
  obtain ⟨T2, Δ, hinΔ, hΔℋ⟩ := hinℋ
  obtain ⟨h1, h2, h3⟩ := hD
  have := h3 Γ hΓ𝒢 Δ hΔℋ
  simp [Env.disjoint] at this
  have hnΓ := Env.mem_pair_fst_in_names T1 hinΓ
  have hnΔ := Env.mem_pair_fst_in_names T2 hinΔ
  rw [Finset.disjoint_left] at this
  exact this hnΓ hnΔ

lemma HyperEnv.merge_nilL (𝒢 : HyperEnv) : [] |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_nilR (𝒢 : HyperEnv) : 𝒢 |ₕ [] = 𝒢 := by simp

lemma HyperEnv.Perm.merge_right {𝒢 ℋ : HyperEnv} (p : 𝒢 ~ ℋ) : ∀ 𝒥, 𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 := by
  induction p
  case nil => simp
  case cons hPE hPH ih => intro 𝒥 ; exact HyperEnv.Perm.cons hPE (ih 𝒥)
  case swap => intro 𝒥 ; exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => intro 𝒥 ; exact HyperEnv.Perm.trans (ih1 𝒥) (ih2 𝒥)

theorem HyperEnv.Perm.merge_left {𝒢 ℋ : HyperEnv} : 𝒢 ~ ℋ → ∀ 𝒥, 𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ := by
  intro h 𝒥
  induction 𝒥
  case nil => exact h
  case cons Γ ℐ ih => apply HyperEnv.Perm.cons (.refl _) ih

theorem HyperEnv.Perm.merge {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
  𝒢 |ₕ ℋ ~ 𝒢' |ₕ ℋ' := (p₁.merge_right ℋ).trans (p₂.merge_left _)

@[simp] lemma HyperEnv.Perm_middle {Γ : Env} : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ Γ :: ℋ ~ Γ :: (𝒢 |ₕ ℋ)
  | [], _ => .refl _
  | Δ :: _, _ =>
    (HyperEnv.Perm.cons (.refl _) Perm_middle).trans (HyperEnv.Perm.swap Δ Γ _)

lemma HyperEnv.Perm.merge_exchange_right {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (𝒢 |ₕ ℋ ~ 𝒢 |ₕ 𝒥) := by
  intro h
  induction 𝒢
  case nil => simp ; exact h
  case cons ih => apply HyperEnv.Perm.cons (by rfl) ih

lemma HyperEnv.Perm.merge_exchange_left {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (ℋ |ₕ 𝒢 ~ 𝒥 |ₕ 𝒢 ) := by
  intro h
  induction h
  case nil => simp
  case cons hPE hPH ih => exact HyperEnv.Perm.cons hPE ih
  case swap => exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

lemma HyperEnv.Perm.merge_comm : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ ℋ ~ ℋ |ₕ 𝒢
  | [], _ => by simp
  | _ :: _, _ => (HyperEnv.Perm.merge_comm.cons (.refl _)).trans HyperEnv.Perm_middle.symm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp only [List.append_assoc]

lemma HyperEnv.Perm.merge_assoc (𝒢 ℋ ℐ : HyperEnv) :
  (𝒢 |ₕ (ℋ |ₕ ℐ)) ~ (ℋ |ₕ (𝒢 |ₕ ℐ)) := by
  repeat rw [← HyperEnv.merge_assoc]
  apply HyperEnv.Perm.merge_right HyperEnv.Perm.merge_comm

lemma HyperEnv.Perm.merge_cons {Γ : Env} {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
    𝒢 |ₕ Γ :: ℋ ~ 𝒢' |ₕ Γ :: ℋ' := p₁.merge (p₂.cons (.refl _))

@[simp] lemma HyperEnv.Perm_merge_singleton (Γ : Env) (𝒢 : HyperEnv) : 𝒢 |ₕ [Γ] ~ Γ :: 𝒢 :=
  HyperEnv.Perm_middle.trans <| by rw [HyperEnv.merge_nilR]

theorem HyperEnv.Perm_merge_comm_assoc (𝒢 ℋ 𝒥 : HyperEnv) :
    (𝒢 |ₕ (ℋ |ₕ 𝒥)) ~ (ℋ |ₕ (𝒢 |ₕ 𝒥)) := by
  simpa only [List.append_assoc] using HyperEnv.Perm.merge_comm.merge_right _

lemma HyperEnv.cons_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢) ~ (𝒢 |ₕ [Γ]) := by
  symm ; apply HyperEnv.Perm_merge_singleton

lemma HyperEnv.cons_append {𝒢 : HyperEnv} {Γ : Env} :
  Γ :: 𝒢 = [Γ] |ₕ 𝒢 := by simp

inductive HyperEnv.Delete (Γ : Env) : HyperEnv → HyperEnv → Prop where
  | head {𝒢 : HyperEnv} {Δ : Env} :
      (Γ ~ Δ) → Delete Γ (Δ :: 𝒢) 𝒢
  | tail {Δ : Env} {𝒢 𝒢' : HyperEnv} :
      Delete Γ 𝒢 𝒢' → Delete Γ (Δ :: 𝒢) (Δ :: 𝒢')

-- Removing Γ from Γ :: 𝒢 => 𝒢 then adding Γ again => Γ :: 𝒢
lemma HyperEnv.Delete_restore {Γ : Env} {𝒢 𝒢' : HyperEnv} (h : Delete Γ 𝒢 𝒢') :
  Γ :: 𝒢' ~ 𝒢 := by
  induction h
  case head Δ hEnv =>
    exact HyperEnv.Perm.cons hEnv (.refl _)
  case tail Δ hD ih =>
    apply HyperEnv.Perm.trans (HyperEnv.Perm.swap ..)
    exact HyperEnv.Perm.cons (List.Perm.refl _) ih

lemma HyperEnv.Perm_Delete {𝒢 ℋ : HyperEnv} (hP : 𝒢 ~ ℋ) :
  ∀ {Γ 𝒢'}, Delete Γ 𝒢 𝒢' → ∃ ℋ', Delete Γ ℋ ℋ' ∧ 𝒢' ~ ℋ' := by
  induction hP
  case nil => intros _ 𝒢 _ ; use 𝒢
  case cons Γ Δ 𝒢 ℋ hPE hPH ih =>
    intros Ξ 𝒥 hDel
    cases hDel
    case head hP' =>
      exact ⟨ℋ, HyperEnv.Delete.head (List.Perm.trans hP' hPE), hPH⟩
    case tail 𝒥 hDel =>
      obtain ⟨ℋ', hDelℋ', hPℋ'⟩ := ih hDel
      exact ⟨Δ :: ℋ', HyperEnv.Delete.tail hDelℋ', HyperEnv.Perm.cons hPE hPℋ'⟩
  case swap Γ Δ 𝒢 =>
    intro Ξ 𝒢' hDel
    cases hDel
    case head hEnv =>
      exact ⟨Δ :: 𝒢, HyperEnv.Delete.tail (HyperEnv.Delete.head hEnv), .refl _⟩
    case tail hD_tail =>
      cases hD_tail
      case head hPE =>
        use Γ :: 𝒢
        exact ⟨HyperEnv.Delete.head hPE, .refl _⟩
      case tail 𝒢' hD_tl_tl =>
        exact ⟨Δ :: Γ :: 𝒢', HyperEnv.Delete.tail (HyperEnv.Delete.tail hD_tl_tl), .swap ..⟩
  case trans ih1 ih2 =>
    intros E1 H1 hDel1
    obtain ⟨H2, hDel2, hP12⟩ := ih1 hDel1
    obtain ⟨H3, hDel3, hP23⟩ := ih2 hDel2
    exact ⟨H3, hDel3, HyperEnv.Perm.trans hP12 hP23⟩

lemma HyperEnv.Perm.cons_cancel_left {Γ : Env} {𝒢 ℋ : HyperEnv} (hP : Γ :: 𝒢 ~ Γ :: ℋ) :
  𝒢 ~ ℋ := by
  have hDel1 : Delete Γ (Γ :: 𝒢) 𝒢 := Delete.head (List.Perm.refl _)
  obtain ⟨_, hDel2, hP'⟩ := HyperEnv.Perm_Delete hP hDel1
  cases hDel2
  case head _ => exact hP'
  case tail hDel3 =>
    apply HyperEnv.Perm.trans hP'
    exact HyperEnv.Delete_restore hDel3

lemma HyperEnv.Perm_merge_cancel_right {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 → 𝒢 ~ ℋ := by
  intro h
  induction 𝒥 generalizing 𝒢 ℋ
  case nil => simp at h ; exact h
  case cons Γ 𝒥 ih =>
    rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc] at h
    have hcancel := (ih h)
    have h_front : Γ :: 𝒢 ~ Γ :: ℋ := by
      apply HyperEnv.Perm.trans (HyperEnv.Perm_merge_singleton Γ 𝒢).symm
      apply HyperEnv.Perm.trans hcancel
      exact HyperEnv.Perm_merge_singleton Γ ℋ
    exact HyperEnv.Perm.cons_cancel_left h_front

lemma HyperEnv.Perm_merge_cancel_left {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ → 𝒢 ~ ℋ := by
  intro h
  induction 𝒥
  case nil => exact h
  case cons Ξ 𝒥' ih => exact ih (HyperEnv.Perm.cons_cancel_left h)
lemma HyperEnv.disjoint_names_left {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint 𝒢.names S ↔ ∀ Γ ∈ 𝒢, Disjoint Γ.names S := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

lemma HyperEnv.disjoint_names_right {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint S 𝒢.names ↔ ∀ Γ ∈ 𝒢, Disjoint S Γ.names := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

def HyperEnv.Linearity (𝒢 : HyperEnv) : Prop :=
  𝒢.Nodup ∧ 𝒢.PairwiseDisjoint

lemma HyperEnv.Perm_preserves_Linearity {𝒢 ℋ : HyperEnv} :
  𝒢 ~ ℋ → (𝒢.Linearity ↔ ℋ.Linearity) := by
  intro h
  simp [HyperEnv.Linearity, HyperEnv.PairwiseDisjoint]
  rw [HyperEnv.Nodup_perm_iff h, HyperEnv.Perm_PairwiseDisjoint_iff h]

lemma HyperEnv.Perm.preserves_Linearity {𝒢 ℋ : HyperEnv}
  (hP : 𝒢 ~ ℋ) (h : 𝒢.Linearity) : ℋ.Linearity :=
  (HyperEnv.Perm_preserves_Linearity hP).mp h

@[simp] lemma HyperEnv.Linearity_nil :
  HyperEnv.Linearity [] := by simp [HyperEnv.Linearity]

@[simp] lemma HyperEnv.Linearity_singleton {Γ : Env} :
  HyperEnv.Linearity [Γ] = Γ.Nodup := by
  simp [HyperEnv.Linearity, HyperEnv.Nodup]

@[simp] lemma HyperEnv.Linearity_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).Linearity = (𝒢.Linearity ∧ ℋ.Linearity ∧
    ∀ a ∈ 𝒢, ∀ b ∈ ℋ, Disjoint a.names b.names) := by
  simp [HyperEnv.Linearity]
  constructor
  · intro h
    obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
    exact ⟨⟨h1, h3⟩, ⟨⟨h2, h4⟩, h5⟩⟩
  · intro h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
    exact ⟨⟨h1, h3⟩, h2, h4, h5⟩

lemma HyperEnv.Perm_rotate_rhs_right {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ 𝒥 |ₕ 𝒦 → 𝒢 ~ 𝒥 |ₕ 𝒦 |ₕ ℋ := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.trans
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge_assoc
    · simp only [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge_left
      exact HyperEnv.Perm.merge_comm

lemma HyperEnv.Perm_rotate_rhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ 𝒥 |ₕ 𝒦 → 𝒢 ~ 𝒦 |ₕ ℋ |ₕ 𝒥 := by
  intro h
  apply HyperEnv.Perm_rotate_rhs_right
  exact HyperEnv.Perm_rotate_rhs_right h

lemma HyperEnv.Perm_pull_rhs_mid_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ ℋ |ₕ (𝒥 |ₕ 𝒦) → 𝒢 ~ 𝒥 |ₕ (ℋ |ₕ 𝒦) := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.merge_assoc

lemma HyperEnv.Perm_pull_rhs_mid_right {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  𝒢 ~ (ℋ |ₕ 𝒥) |ₕ 𝒦 → 𝒢 ~ (ℋ |ₕ 𝒦) |ₕ 𝒥 := by
  intro h
  apply HyperEnv.Perm.trans
  · exact h
  · apply HyperEnv.Perm.symm
    conv_rhs => rw [HyperEnv.merge_assoc]
    apply HyperEnv.Perm_pull_rhs_mid_left
    conv_rhs => rw [← HyperEnv.merge_assoc]
    apply HyperEnv.Perm_rotate_rhs_left
    rfl

lemma HyperEnv.Perm.exchange_lhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  ℋ ~ 𝒥 → ℋ |ₕ 𝒦 ~ 𝒢 → 𝒥 |ₕ 𝒦 ~ 𝒢 := by
  intros h1 h2
  exact (h2.symm.trans (HyperEnv.Perm.merge_right h1 _)).symm

lemma HyperEnv.Perm.exchange_rhs_left {𝒢 ℋ 𝒥 𝒦 : HyperEnv} :
  ℋ ~ 𝒥 → 𝒢 ~ ℋ |ₕ 𝒦 → 𝒢 ~ 𝒥 |ₕ 𝒦 := by
  intros h1 h2
  exact (h2.trans (HyperEnv.Perm.merge_right h1 _))

lemma Env.exists_perm_cons {Γ : Env} {x : FPName} {A : Types} (h : (x, A) ∈ Γ) :
  ∃ Δ, Γ ~ (x, A) :: Δ := by
  induction Γ
  case nil => simp at h
  case cons e Ξ ih =>
    simp at h
    cases h
    case inl h => subst h ; use Ξ
    case inr h =>
      obtain ⟨y, T⟩ := e
      obtain ⟨Ξ', hP⟩ := ih h
      use (y ∶ T :: Ξ')
      apply List.Perm.trans
      · apply List.Perm.cons
        exact hP
      · apply List.Perm.swap

lemma HyperEnv.Perm_exchange_lhs {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒢 ~ 𝒥 → ℋ ~ 𝒥:= by
   intro h1 h2
   exact h1.symm.trans h2

lemma HyperEnv.Perm_exchange_rhs {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒥 ~ 𝒢 → 𝒥 ~ ℋ := by
   intro h1 h2
   exact h2.trans h1

lemma HyperEnv.Perm_merge_cancel_right_inv {𝒢 ℋ 𝒥 : HyperEnv} :
   𝒢 ~ ℋ → 𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 := by
  intro h
  induction 𝒥 generalizing 𝒢 ℋ
  case nil => simp ; exact h
  case cons E HE ih =>
    have hG : E :: (𝒢 |ₕ HE) ~ 𝒢 |ₕ E :: HE := HyperEnv.Perm_middle.symm
    have hH : E :: (ℋ |ₕ HE) ~ ℋ |ₕ E :: HE := HyperEnv.Perm_middle.symm
    apply HyperEnv.Perm_exchange_lhs hG
    apply HyperEnv.Perm_exchange_rhs hH
    apply HyperEnv.Perm.cons
    · rfl
    · exact ih h

lemma HyperEnv.Perm_merge_cancel_left_inv {𝒢 ℋ 𝒥 : HyperEnv} :
  𝒢 ~ ℋ → 𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ := by
  intro h
  induction 𝒥
  case nil => exact h
  case cons ih =>
    apply HyperEnv.Perm.cons
    · rfl
    · exact ih

lemma HyperEnv.Perm_merge_comm_assoc_rhs (𝒢 ℋ 𝒥 𝒦 : HyperEnv) :
  𝒢 ~ (ℋ |ₕ (𝒦 |ₕ 𝒥)) → 𝒢 ~ (𝒦 |ₕ (ℋ |ₕ 𝒥)) := by
  intro h
  exact h.trans (HyperEnv.Perm_merge_comm_assoc ℋ 𝒦 𝒥)

lemma HyperEnv.Perm_merge_comm_assoc_lhs (𝒢 ℋ 𝒥 𝒦 : HyperEnv) :
  (ℋ |ₕ (𝒦 |ₕ 𝒥)) ~ 𝒢 → (𝒦 |ₕ (ℋ |ₕ 𝒥)) ~ 𝒢 := by
  intro h
  exact (HyperEnv.Perm_merge_comm_assoc_rhs 𝒢 ℋ 𝒥 𝒦 h.symm).symm

lemma HyperEnv.exists_perm_cons_of_mem {𝒢 : HyperEnv} {Γ : Env} (h : Γ ∈ 𝒢) :
  ∃ 𝒢', 𝒢 ~ Γ :: 𝒢' := by
  induction 𝒢
  case nil => contradiction
  case cons hd tl ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h_in_tl
    · exact ⟨tl, HyperEnv.Perm.refl _⟩
    · obtain ⟨tl', hP⟩ := ih h_in_tl
      use hd :: tl'
      apply HyperEnv.Perm.trans
      · exact HyperEnv.Perm.cons (.refl _) hP
      · exact HyperEnv.Perm.swap hd Γ tl'

lemma HyperEnv.Perm_nil_inv {𝒢 : HyperEnv} :
  𝒢.Perm [] ↔ 𝒢 = [] := by
  constructor
  · intro h
    generalize h1 : [] = ℋ at h
    induction h <;> simp_all
  · intro h ; subst h ; simp

lemma HyperEnv.Perm_singleton_inv {Γ : Env} {ℋ : HyperEnv} (h : ([Γ] : HyperEnv) ~ ℋ) :
  ∃ Δ, ℋ = [Δ] ∧ Γ ~ Δ := by
  generalize heq : ([Γ] : HyperEnv) = G at h
  induction h generalizing Γ
  case nil => simp only [List.cons_ne_self] at heq
  case cons E1 E2 H1 H2 hPE ih =>
    simp_all only [List.cons.injEq, List.nil_eq, ↓existsAndEq, true_and, and_true,
      List.cons_ne_self, not_isEmpty_of_nonempty, IsEmpty.exists_iff, implies_true]
    obtain ⟨h1, h2⟩ := heq
    subst h1 h2
    exact HyperEnv.Perm_nil_inv.mp hPE.symm
  case swap => simp only [List.cons.injEq, List.nil_eq, reduceCtorEq, and_false] at heq
  case trans hP1 hP2 ih1 ih2 =>
    obtain ⟨Δ, hΔ, hP1⟩ := ih1 heq
    obtain ⟨Ξ, hΞ, hP2⟩ := ih2 hΔ.symm
    exact ⟨Ξ, hΞ, hP1.trans hP2⟩

lemma HyperEnv.Perm_singleton_singleton {Γ Δ : Env} :
  ([Γ] : HyperEnv) ~ [Δ] ↔ Γ ~ Δ := by
  constructor
  · intro h
    obtain ⟨Δ', heq, hP⟩ := HyperEnv.Perm_singleton_inv h
    injection heq with hhd
    subst hhd
    exact hP
  · intro h ; exact HyperEnv.Perm.cons h HyperEnv.Perm.nil

lemma HyperEnv.mem_of_mem_mem_names {𝒢 : HyperEnv} {Γ : Env} {x : FPName} {A : Types}
  (h₁ : x ∶ A ∈ Γ) (h₂ : Γ ∈ 𝒢) : x ∈ 𝒢.names := by
  induction 𝒢
  case nil => simp_all only [List.not_mem_nil]
  case cons E HE ih =>
    simp only [List.mem_cons] at h₂
    cases h₂
    case inl h =>
      subst h
      simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
      apply Or.inl
      use A
    case inr h =>
      simp only [names_cons, Finset.mem_union, Env.mem_pair_fst_in_names_iff]
      apply Or.inr
      apply ih h

lemma HyperEnv.not_mem_names_iff {𝒢 : HyperEnv} {x : FPName} :
  x ∉ 𝒢.names ↔ ∀ (Γ : Env) (A : Types), Γ ∈ 𝒢 → (x, A) ∉ Γ := by
  induction 𝒢
  case nil =>
    simp only [names_nil, Finset.notMem_empty, not_false_eq_true, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  case cons E HE ih =>
    constructor
    · intro h1 Γ A hin
      simp only [names_cons, Finset.mem_union, not_or, List.mem_cons] at h1 hin
      obtain ⟨hE, hHE⟩ := h1
      cases hin
      case inl h =>
        subst h
        exact Env.not_mem_names_iff.mp hE A
      case inr h =>
        exact ih.mp hHE Γ A h
    · intro h
      have h' := h E
      simp only [List.mem_cons, true_or, forall_const, names_cons, Finset.mem_union,
        Env.mem_pair_fst_in_names_iff, not_or, not_exists] at h h' ⊢
      constructor
      · have := Env.not_mem_names_iff.mpr h'
        simp only [Env.mem_pair_fst_in_names_iff, not_exists] at this
        exact this
      · apply ih.mpr
        intro Γ A hin
        exact h Γ A (Or.inr hin)

lemma HyperEnv.PairwiseDisjoint_tail_not_in_head {𝒢 ℋ : HyperEnv} :
  List.Pairwise Env.disjoint (𝒢 |ₕ ℋ) →
  (∀ E, E ∈ ℋ → ∀ x A, (x ∶ A) ∈ E → x ∉ 𝒢.names) := by
  intros h Γ hΓinℋ x A hinΓ hxin𝒢
  have h_cross := (List.pairwise_append.mp h).2.2
  obtain ⟨B, Δ, hinΔ, hΔin𝒢⟩ := HyperEnv.mem_pair_fst_in_names.mp hxin𝒢
  have hxΓ : x ∈ Γ.names := Env.mem_pair_fst_in_names _ hinΓ
  have hxΔ : x ∈ Δ.names := Env.mem_pair_fst_in_names _ hinΔ
  have hD := h_cross Δ hΔin𝒢 Γ hΓinℋ
  exact Finset.disjoint_left.mp hD hxΔ hxΓ

lemma HyperEnv.substNames_res_left
  {𝒢 : HyperEnv} {Γ Δ : Env} {x z w : FPName} {A B : Types}
  (hx𝒢 : x ∉ 𝒢.names) (hxΓ : x ∉ Γ.names) (hxΔ : x ∉ Δ.names) (hxw : x ≠ w) :
  ∀ Ξ ∈ 𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (x, C) ∈ Ξ → x = z := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hx𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · rfl
    · exfalso
      exact hxΓ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exfalso
      exact hxw rfl
    · exfalso
      exact hxΔ (Env.mem_pair_fst_in_names _ h)

lemma HyperEnv.substNames_res_right
  {𝒢 : HyperEnv} {Γ Δ : Env} {x y w : FPName} {A B : Types}
  (hy𝒢 : y ∉ 𝒢.names) (hyΓ : y ∉ Γ.names) (hyΔ : y ∉ Δ.names) (hyx : y ≠ x) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [w ∶ B :: Δ], ∀ C, (y, C) ∈ Ξ → y = w := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl
  · exfalso
    exact hy𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exfalso
      exact hyx rfl
    · exfalso
      exact hyΓ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · rfl
    · exfalso
      exact hyΔ (Env.mem_pair_fst_in_names _ h)

lemma HyperEnv.mem_names_subset_of_perm_single {𝒢 : HyperEnv} {E Γ : Env} {x : FPName} {A : Types}
  (hE𝒢 : E ∈ 𝒢) (hPE : E ~ x ∶ A :: Γ) :
  Γ.names ⊆ 𝒢.names := by
  have hNames := HyperEnv.names_eq_of_perm (HyperEnv.Perm_singleton_singleton.mpr hPE)
  simp at hNames
  have hΓsub : Γ.names ⊆ 𝒢.names := by
    have hs1 : (Γ.names) ⊆ (insert x Γ.names) := Finset.subset_insert _ _
    rw [← hNames] at hs1
    exact hs1.trans (HyperEnv.subset_names_of_mem hE𝒢)
  exact hΓsub

lemma HyperEnv.mem_names_subset_of_perm {𝒢 : HyperEnv} {E Γ Δ : Env} {x : FPName} {A : Types}
  (hE𝒢 : E ∈ 𝒢) (hPE : E ~ x ∶ A :: Γ‚ Δ) :
  Γ.names ⊆ 𝒢.names ∧ Δ.names ⊆ 𝒢.names := by
  have hNames := HyperEnv.names_eq_of_perm (HyperEnv.Perm_singleton_singleton.mpr hPE)
  simp at hNames
  have hΓsub : Γ.names ⊆ 𝒢.names := by
    have hs1 : (Γ.names ∪ Δ.names) ⊆ insert x (Γ.names ∪ Δ.names) := Finset.subset_insert _ _
    have hs2 : Γ.names ⊆ (Γ.names ∪ Δ.names) := Finset.subset_union_left
    have := hs2.trans hs1
    rw [← hNames] at this
    exact this.trans (HyperEnv.subset_names_of_mem hE𝒢)
  have hΔsub : Δ.names ⊆ 𝒢.names := by
    have hs1 : (Γ.names ∪ Δ.names) ⊆ insert x (Γ.names ∪ Δ.names) := Finset.subset_insert _ _
    have hs2 : Δ.names ⊆ (Γ.names ∪ Δ.names) := Finset.subset_union_right
    have := hs2.trans hs1
    rw [← hNames] at this
    exact this.trans (HyperEnv.subset_names_of_mem hE𝒢)
  exact ⟨hΓsub, hΔsub⟩

lemma HyperEnv.absurd_fresh_of_mem_perm {𝒢 ℋ : HyperEnv} {C : Env} {v : FPName} {T : Types}
  (h𝒢 : 𝒢 ~ ℋ) (hC : C ∈ ℋ) (hv : (v, T) ∈ C) (hFv : v ∉ 𝒢.names) :
  False := by
  obtain ⟨Ex, hEx_in_𝒢, hPEx⟩ := HyperEnv.Perm_mem h𝒢 hC
  have hvEx : (v, T) ∈ Ex := (List.Perm.mem_iff hPEx).mpr hv
  have hvExNames := Env.mem_pair_fst_in_names _ hvEx
  exact hFv (HyperEnv.subset_names_of_mem hEx_in_𝒢 hvExNames)

lemma HyperEnv.mem_tensor_parr_post_env
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ], ∀ C, (z, C) ∈ Ξ →
  z = x ∨ z = x' ∨ z = y ∨ z = y' := by
  intros Ξ hΞ C hin
  simp at hΞ
  rcases hΞ with h1 | rfl | rfl | rfl
  · exfalso
    exact hz𝒢 (HyperEnv.mem_of_mem_mem_names hin h1)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exact Or.inl rfl
    · exfalso
      exact hzΓ₁ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | h
    · exact Or.inr (Or.inl rfl)
    · exfalso
      exact hzΓ₂ (Env.mem_pair_fst_in_names _ h)
  · simp at hin
    rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exfalso
      exact hzΔ (Env.mem_pair_fst_in_names _ h)

lemma HyperEnv.substNames_tensor_parr_x
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx' : z ≠ x') (hzy' : z ≠ y') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = x := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact h
  · exact False.elim (hzx' h)
  · exact False.elim (hzy h)
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_x'
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzy' : z ≠ y') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = x' := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact h
  · exact False.elim (hzy h)
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_y
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzx' : z ≠ x') (hzy' : z ≠ y') :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = y := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact False.elim (hzx' h)
  · exact h
  · exact False.elim (hzy' h)

lemma HyperEnv.substNames_tensor_parr_y'
  {𝒢 : HyperEnv} {Γ₁ Γ₂ Δ : Env} {x x' y y' z : FPName} {A B : Types}
  (hz𝒢 : z ∉ 𝒢.names) (hzΓ₁ : z ∉ Γ₁.names) (hzΓ₂ : z ∉ Γ₂.names) (hzΔ : z ∉ Δ.names)
  (hzx : z ≠ x) (hzx' : z ≠ x') (hzy : z ≠ y) :
  ∀ Ξ ∈ 𝒢 |ₕ [x ∶ B :: Γ₁] |ₕ [x' ∶ A :: Γ₂] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Δ],
    ∀ C, (z, C) ∈ Ξ → z = y' := by
  intros Ξ hΞ C hin
  rcases HyperEnv.mem_tensor_parr_post_env hz𝒢 hzΓ₁ hzΓ₂ hzΔ Ξ hΞ C hin with h | h | h | h
  · exact False.elim (hzx h)
  · exact False.elim (hzx' h)
  · exact False.elim (hzy h)
  · exact h

lemma HyperEnv.PairwiseDisjoint_implies_disjoint {Γ Δ : Env} :
  HyperEnv.PairwiseDisjoint [Γ, Δ] → Γ.disjoint Δ := by
  simp [HyperEnv.PairwiseDisjoint]
