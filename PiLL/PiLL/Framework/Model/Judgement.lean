import PiLL.Framework.Model.Environment
import PiLL.Framework.Model.Alpha
import PiLL.Framework.Model.Congruence

-- FIXME: Added a lot of extra contranints so facilitate Env / HyperEnv disjointness
-- as well as no pathological process appearing e.g. x(x).P, x[DUP](x).P etc.

inductive Typing : HyperEnv → Proc → Prop where
  | mix₀ :
      ----------
      Typing ∅ 𝟘

  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {hDisj : 𝒢.disjoint ℋ}:
      Typing 𝒢 P → Typing ℋ Q →
      --------------------------
      Typing (𝒢 |ₕ ℋ) (P |ₚ Q)

  | cut (𝒢 : HyperEnv) (Γ Δ : Env) (P : Proc) (x y : PName) (A : Types)
      {hFresh: x ∉ 𝒢.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧
        y ∉ 𝒢.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names}
      {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
      Typing (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) P →
      -------------------------------------
      Typing (𝒢 |ₕ Γ‚ Δ) (𝑣⸨x, y⸩ P)

  | tensor {Γ Δ : Env} {P : Proc} {x y : PName} {B A : Types}
      {hFresh : x ∉ Γ.names ∧ x ∉ Δ.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names}
      {hneq : x ≠ y} {hDisj: Γ.disjoint Δ} :
      Typing (Γ‚ y ∶ A |ₕ Δ‚ x ∶ B) P →
      ---------------------------------
      Typing (Γ‚ Δ‚ x ∶ A ⨂ B) (x⟦y⟧․P)

  | one {P : Proc} {x : PName} :
      Typing ∅ P →
      ----------------------
      Typing (x ∶ 1) (x⟦⟧․P)

  | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types}
      {hFresh : x ∉ Γ.names ∧ y ∉ Γ.names}
      {hneq : x ≠ y} :
      Typing (Γ‚ y ∶ A‚ x ∶ B) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⅋ B) (x⸨y⸩․P)

  | bot {Γ : Env} {P : Proc} {x : PName} {hFresh : x ∉ Γ.names} :
      Typing Γ P →
      --------------------------
      Typing (Γ‚ x ∶ ⊥) (x⸨⸩․P)

  | oplus₁
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐋⟧․P)

  | oplus₂
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ B) P →
      ------------------------------
      Typing (Γ‚ x ∶ A ⊕ B) (x⟦𝐑⟧․P)

  | amp
      {Γ : Env} {P Q : Proc} {x : PName} {A B : Types} :
      Typing (Γ‚ x ∶ A) P → Typing (Γ‚ x ∶ B) Q →
      ---------------------------------------------
      Typing (Γ‚ x ∶ A & B) (x․case{𝐋 : P, 𝐑 : Q})

  | quest
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P →
      -----------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦USE⟧․P)

  | w
      {Γ : Env} {P : Proc} {x : PName} {A : Types} {hFrehs : x ∉ Γ.names} :
      Typing Γ P →
      -----------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦DISP⟧․P)

  | c
      {Γ : Env} {P : Proc} {x x' : PName} {A : Types}
      {hneq : x ≠ x'} {hf : x ∉ Γ.names ∧ x' ∉ Γ.names} :
      Typing (Γ‚ x ∶ ??A‚ x' ∶ ??A) P →
      ---------------------------------
      Typing (Γ‚ x ∶ ??A) (x⟦DUP⟧⸨x'⸩․P)

  | bang
      {Γ : Env} {P : Proc} {x : PName} {A : Types} :
      Typing (Γ‚ x ∶ A) P → ?ₑΓ →
      ------------------------------
      Typing (Γ‚ x ∶ !!A) (!x․{P})

  | exists_
      {Γ : Env} {P : Proc} {x : PName} {A B : Types} {X : TVar} :
      Typing (Γ‚ x ∶ B{A // X}) P →
      -----------------------------
      Typing (Γ‚ x ∶ ∃X․B) (x⟦A⟧․P)

  | forall_
      {Γ : Env} {P : Proc} {x : PName} {B : Types} {X : TVar} :
      Typing (Γ‚ x ∶ B) P → X ∉ ft(Γ)ₑ →
      ---------------------------------
      Typing (Γ‚ x ∶ ∀X․B) (x⸨X⸩․P)

  | ax
      {x y : PName} {A : Types} {hneq : x ≠ y} :
      Typing (x ∶ Aᗮ‚ y ∶ A) (x ⟷ₚ y)

notation:50 "⊢ " P " ∷ " T => Typing T P

-- Projection of a Judgement to its process
def proc {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : Proc := P

-- Projection of a Judgement to its environment
def env {𝒢 : HyperEnv} {P : Proc} (_ : ⊢ P ∷ 𝒢) : HyperEnv := 𝒢

lemma Typing.f_subset_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
  P.f ⊆ 𝒢.names := by
  induction h

  case mix₀ => rfl

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

lemma Typing.names_subset_f {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
  𝒢.names ⊆ P.f := by
  induction h

  case mix₀ => rfl

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
    apply Finset.Subset.trans ih
    apply Finset.subset_union_right

  case amp ihP ihQ =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.Subset.trans ihP
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right

  case c ih =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton] at *
    apply Finset.union_subset
    · apply Finset.Subset.trans _ Finset.subset_union_right
      apply Finset.subset_sdiff.mpr
      constructor
      · apply Finset.Subset.trans _ ih
        rw [Finset.union_assoc]
        exact Finset.subset_union_left
      · simp_all
    · exact Finset.subset_union_left

  case ax =>
    simp only [Proc.f, HyperEnv.names_singleton, Env.names_distributes,
      Env.names_singleton, Finset.union_singleton]
    simp [Finset.pair_comm]

  case cut hf _ _ _ ih =>
    simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    rw [Finset.mem_sdiff]
    apply And.intro
    · apply ih
      simp_all
    · simp_all
      apply And.intro
      all_goals
        intro heq
        rw [heq] at ha
        exact hf.1 (by simp_all)

  case tensor ih | parr ih =>
    simp only [Proc.f, HyperEnv.names_distributes, HyperEnv.names_singleton,
      Env.names_distributes, Env.names_singleton] at *
    intro a ha
    simp at ⊢ ha ih
    rcases ha with rfl | h
    · left ; rfl
    · apply Or.inr
      apply And.intro
      · apply ih
        simp_all
      · intro heq
        rw [heq] at h
        simp_all

lemma Typing.f_eq_names {𝒢 : HyperEnv} {P : Proc} {h : ⊢ P ∷ 𝒢} :
  P.f = 𝒢.names := by
  exact Finset.Subset.antisymm (Typing.f_subset_names h) (Typing.names_subset_f h)

lemma HyperEnv.not_mem_of_fresh_name {𝒢 : HyperEnv} {Γ : Env} {P : Proc} {x : PName}
  {A : Types} (hf : x ∉ P.f) (hP : ⊢ P ∷ 𝒢) : Γ‚ x ∶ A ∉ 𝒢 := by
  let Ex := Γ‚ x ∶ A
  intro hc
  have hx : x ∈ 𝒢.names := by
    rw [HyperEnv.names, Finset.mem_biUnion]
    use Ex
    simp [hc, Ex, Env.names_distributes]
  exact hf (Typing.names_subset_f hP hx)

lemma HyperEnv.names_subset_self {𝒢 : HyperEnv} {Γ : Env} (h : Γ ∈ 𝒢) :
  Γ.names ⊆ 𝒢.names := by
  simp [HyperEnv.names, Env.names]
  apply Finset.subset_biUnion_of_mem (fun E => Env.names E) h

lemma Typing.preserves_disjoint {𝒢 ℋ : HyperEnv} {P : Proc} {h : ⊢ P ∷ 𝒢 |ₕ ℋ} :
  𝒢.disjoint ℋ := by
  generalize heq : 𝒢 |ₕ ℋ = 𝒥
  rw [heq] at h
  cases h
  all_goals
  sorry



theorem Typing.cut_inversion {𝒢 : HyperEnv} {P : Proc} {x y : PName}
  (h : ⊢ 𝑣⸨x, y⸩ P ∷ 𝒢) : ∃ Γ Δ A 𝒢_ctx,
    𝒢 = 𝒢_ctx |ₕ {Γ‚ Δ} ∧
    x ∉ 𝒢_ctx.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧
    y ∉ 𝒢_ctx.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names ∧
    x ≠ y ∧ Γ.disjoint Δ ∧
    ⊢ P ∷ 𝒢_ctx |ₕ {Γ‚ x ∶ A} |ₕ {Δ‚ y ∶ Aᗮ} := by
  generalize hG : 𝒢 = 𝒢_in at h
  cases h

  case cut 𝒢' Γ' Δ' A' hd hf hneq 𝒟' =>
    subst hG
    simp at *
    exists Γ', Δ', A', 𝒢'
    refine ⟨rfl, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2,
      hneq, hd, 𝒟'⟩



theorem Typing.respects_cong {𝒢 : HyperEnv} {P Q : Proc}
  (hcong : P ≡ₚ Q) : (⊢ P ∷ 𝒢) ↔ (⊢ Q ∷ 𝒢) := by
  induction hcong generalizing 𝒢

  case refl => rfl

  case symm ih => exact ih.symm

  case trans h1 h2 ihP ihQ => exact Iff.trans ihP ihQ

  case par_congr ih =>
    apply Iff.intro <;>
    · intro h
      cases h
      rename_i hd hP hQ
      apply Typing.mix
      · exact hd
      · (try exact ih.mp hP) ; (try exact ih.mpr hP)
      · exact hQ

  case par_comm =>
    apply Iff.intro
    all_goals
    · intro h
      cases h
      rename_i 𝒢' 𝒢'' hDisj hP hQ
      rw [HyperEnv.merge_comm]
      apply Typing.mix
      · exact hDisj.symm
      · exact hQ
      · exact hP

  case par_assoc =>
    apply Iff.intro
    · intro h
      cases h
      rename_i hPQ hR
      cases hPQ
      rename_i hP hQ
      rw [HyperEnv.merge_assoc]
      apply Typing.mix
      · simp_all [HyperEnv.disjoint]
      · exact hP
      · apply Typing.mix
        · simp_all [HyperEnv.disjoint]
        · exact hQ
        · exact hR
    · intro h
      cases h
      rename_i hP hQR
      cases hQR
      rename_i hQ hR
      rw [← HyperEnv.merge_assoc]
      apply Typing.mix
      · simp_all [HyperEnv.disjoint]
      · apply Typing.mix
        · simp_all [HyperEnv.disjoint]
        · exact hP
        · exact hQ
      · exact hR

  case par_zero =>
    apply Iff.intro
    · intro h
      cases h
      rename_i hDisj hP hQ
      cases hQ
      rw [HyperEnv.merge_unitR]
      exact hP
    · intro h
      rw [← HyperEnv.merge_unitR 𝒢]
      apply Typing.mix
      · simp [HyperEnv.disjoint]
      · exact h
      · apply Typing.mix₀

  case cut_congr ih =>
    apply Iff.intro <;>
    · intro h
      cases h
      rename_i hd hf hneq 𝒟
      apply Typing.cut
      · exact hf
      · exact hneq
      · exact hd
      · (try exact ih.mp 𝒟) ; (try exact ih.mpr 𝒟)

  case cut_scope hf1 =>
    apply Iff.intro
    · intro h
      cases h
      rename_i P Q x y 𝒢 ℋ hd1 hP hQ
      cases hP
      rename_i 𝒢' Γ Δ A hd2 hf hneq 𝒟
      rw [HyperEnv.merge_comm, ← HyperEnv.merge_assoc]
      apply Typing.cut
      · simp only [HyperEnv.names_distributes, Finset.mem_union]
        simp
        repeat' apply And.intro
        · intro hxℋ
          have hxQ := Typing.names_subset_f hQ hxℋ
          exact hf1.1 hxQ
        · exact hf.1
        · exact hf.2.1
        · exact hf.2.2.1
        · intro hyℋ
          have hyQ := Typing.names_subset_f hQ hyℋ
          exact hf1.2 hyQ
        · exact hf.2.2.2.1
        · exact hf.2.2.2.2.1
        · exact hf.2.2.2.2.2
      · exact hneq
      · exact hd2
      · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc, HyperEnv.merge_comm,
            ← HyperEnv.merge_assoc]
        apply Typing.mix
        · simp [HyperEnv.disjoint, HyperEnv.names]
          repeat' apply And.intro
          · intro Γ hΓℋ hxΓ
            have hxℋ : x ∈ ℋ.names := Finset.mem_biUnion.mpr ⟨Γ, hΓℋ, hxΓ⟩
            have hxQ := Typing.names_subset_f hQ hxℋ
            exact hf1.1 hxQ
          · intro Γ hΓℋ hyΓ
            have hyℋ : y ∈ ℋ.names := Finset.mem_biUnion.mpr ⟨Γ, hΓℋ, hyΓ⟩
            have hyQ := Typing.names_subset_f hQ hyℋ
            exact hf1.2 hyQ
          · apply Finset.disjoint_of_subset_left _ hd1
            simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
              Env.names_distributes, ← Finset.union_assoc, Finset.subset_union_right]
          · apply Finset.disjoint_of_subset_left _ hd1
            simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
              Env.names_distributes, ← Finset.union_assoc, Finset.union_comm Γ.names Δ.names,
              Finset.subset_union_right]
          · apply Finset.disjoint_of_subset_left _ hd1
            simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
              Env.names_distributes]
            simp only [HyperEnv.names, Finset.subset_union_left]
        · exact 𝒟
        · exact hQ
    · intro h
      rename_i x y
      cases h
      rename_i P' Q' 𝒢 Γ Δ A hd1 hf hneq 𝒟
      generalize heq : (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) = 𝒥
      rw [heq] at 𝒟
      cases 𝒟
      rename_i 𝒢' ℋ' hd2 hP hQ
      · let Ex := Γ‚ x ∶ A
        let Ey := Δ‚ y ∶ Aᗮ
        let Ctx := ({Ex} : HyperEnv) |ₕ {Ey}

        have hTotal : Ex ∈ (𝒢 |ₕ Ex |ₕ Ey) ∧ Ey ∈ (𝒢 |ₕ Ex |ₕ Ey) := by simp

        rw [heq] at hTotal
        simp [HyperEnv.merge, Finset.mem_union] at hTotal

        have hninℋ' : Ex ∉ ℋ' ∧ Ey ∉ ℋ':=
          ⟨HyperEnv.not_mem_of_fresh_name hf1.1 hQ,
          HyperEnv.not_mem_of_fresh_name hf1.2 hQ⟩

        have hin𝒢' : Ex ∈ 𝒢' ∧ Ey ∈ 𝒢' :=
          ⟨Or.resolve_right hTotal.1 hninℋ'.1,
          Or.resolve_right hTotal.2 hninℋ'.2⟩

        let 𝒢'_base := 𝒢' \ {Ex, Ey}
        have h𝒢' : 𝒢' = 𝒢'_base |ₕ {Ex} |ₕ {Ey} := by
          simp only [𝒢'_base, HyperEnv.merge]
          rw [Finset.union_assoc, Finset.union_comm ({Ex} : HyperEnv) ({Ey} : HyperEnv),
            Finset.union_singleton]
          symm
          apply Finset.sdiff_union_of_subset
          simp [Finset.insert_subset_iff]
          exact ⟨hin𝒢'.1, hin𝒢'.2⟩

        have h𝒢 : 𝒢 = 𝒢'_base |ₕ ℋ' := by
          simp only [h𝒢'] at heq
          rw [HyperEnv.merge_comm _ ℋ', ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc] at heq
          apply Finset.ext
          intro e
          simp only [HyperEnv.merge, Finset.mem_union]
          simp only [HyperEnv.merge] at heq
          constructor
          · intro he𝒢
            have hin : e ∈ 𝒢'_base ∪ ℋ' ∪ Ctx := by
              simp only [Ctx, HyperEnv.merge, ← Finset.union_assoc,
                Finset.union_comm _ ℋ']
              rw [← heq]
              rw [Finset.union_assoc]
              apply Finset.mem_union_left
              exact he𝒢
            simp only [Ctx, HyperEnv.merge, Finset.mem_union] at hin
            rcases hin with h1 | h2
            · exact h1
            · rcases h2
              · rename_i h3
                exfalso
                apply hf.1
                rw [HyperEnv.names, Finset.mem_biUnion]
                rw [Finset.mem_singleton] at h3
                rw [h3] at he𝒢
                use Ex, he𝒢
                simp [Ex, Env.names_distributes]
              · rename_i h4
                exfalso
                apply hf.2.2.2.1
                rw [HyperEnv.names, Finset.mem_biUnion]
                rw [Finset.mem_singleton] at h4
                rw [h4] at he𝒢
                use Ey, he𝒢
                simp [Ey, Env.names_distributes]
          · intro hRHS
            have hin : e ∈ ℋ' ∪ 𝒢'_base ∪ {Ex} ∪ {Ey} := by
              simp only [Finset.mem_union, Finset.mem_singleton]
              rcases hRHS with h1 | h2
              · left ; left ; right ; exact h1
              · left ; left ; left ; exact h2
            rw [← heq] at hin
            simp only [Finset.mem_union, Finset.mem_singleton] at hin
            rcases hin with h𝒢 | rfl | rfl
            · rcases h𝒢 with h1 | rfl
              · exact h1
              · exfalso
                rcases hRHS with h1 | h2
                · simp [𝒢'_base, Ex] at h1
                · exact hninℋ'.1 h2
            · exfalso
              rcases hRHS with h1 | h2
              · simp [𝒢'_base, Ey] at h1
              · exact hninℋ'.2 h2

        have hd' : (𝒢'_base |ₕ {Γ‚ Δ}).disjoint ℋ' := by
          simp only [HyperEnv.disjoint] at *
          simp only [HyperEnv.names_distributes, HyperEnv.names_singleton,
            Env.names_distributes, Finset.disjoint_union_left]
          split_ands
          · apply Finset.disjoint_of_subset_left _ hd2
            rw [h𝒢']
            simp only [HyperEnv.names_distributes, Finset.union_assoc,
              Finset.subset_union_left]
          · apply Finset.disjoint_of_subset_left _ hd2
            have hΓEx : Γ.names ⊆ Ex.names := by simp [Ex]
            have hEx𝒢' : Ex.names ⊆ 𝒢'.names :=
              HyperEnv.names_subset_self hin𝒢'.1
            exact Finset.Subset.trans hΓEx hEx𝒢'
          · apply Finset.disjoint_of_subset_left _ hd2
            have hΔEy : Δ.names ⊆ Ey.names := by simp [Ey]
            have hEy𝒢' : Ey.names ⊆ 𝒢'.names :=
              HyperEnv.names_subset_self hin𝒢'.2
            exact Finset.Subset.trans hΔEy hEy𝒢'

        have hf' : x ∉ 𝒢'_base.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧ y ∉ 𝒢'_base.names
          ∧ y ∉ Γ.names ∧ y ∉ Δ.names := by
          rcases hf with ⟨hx𝒢, hxΓ, hxΔ, hy𝒢, hyΓ, hyΔ⟩
          refine ⟨?_, hxΓ, hxΔ, ?_, hyΓ, hyΔ⟩
          · intro h_contra
            apply hx𝒢
            rw [h𝒢]
            simp only [HyperEnv.names_distributes, Finset.mem_union]
            left
            exact h_contra
          · intro h_contra
            apply hy𝒢
            rw [h𝒢]
            simp only [HyperEnv.names_distributes, Finset.mem_union]
            left
            exact h_contra

        rw [h𝒢, HyperEnv.merge_comm, ← HyperEnv.merge_assoc, HyperEnv.merge_comm _ 𝒢'_base]
        apply Typing.mix
        · exact hd'
        · apply Typing.cut _ _ _ _ _ _ A
          · rw [h𝒢'] at hP
            simp only [Ex, Ey] at hP
            exact hP
          · exact hf'
          · exact hneq
          · exact hd1
        · exact hQ




  case cut_swap P' x y a b hDisj =>
    apply Iff.intro
    · intro h

      obtain ⟨Γ1, Δ1, A1, 𝒢_mid, rfl,
              hx𝒢, hxΓ, hxΔ,
              hy𝒢, hyΓ, hyΔ,
              hneq1, hd1,
              h_prem1⟩ :=
        Typing.cut_inversion h

      obtain ⟨Γ2, Δ2, A2, 𝒢_core, heq_mid,
              ha𝒢, haΓ, haΔ,
              hb𝒢, hbΓ, hbΔ,
              hneq2, hd2,
              h_prem2⟩ :=
        Typing.cut_inversion h_prem1

      have h_source : (Γ2‚ Δ2) ∈ 𝒢_mid |ₕ {Γ1‚ x ∶ A1} |ₕ {Δ1‚ y ∶ A1ᗮ} := by
        rw [heq_mid] ; simp

      -- 4. Generalize the complex environment term to avoid Dependent Elimination failure
      generalize hE : Γ2‚ Δ2 = E_inner
      rw [hE] at h_source

      simp only [HyperEnv.merge, Finset.mem_union, Finset.mem_singleton] at h_source
      rcases h_source with h_indep | h_left | h_right
      ·
        have h_core_eq : 𝒢_core = (𝒢_mid \ {E_inner}) |ₕ {Γ1‚ x ∶ A1} |ₕ {Δ1‚ y ∶ A1ᗮ} := by
          sorry

        rw [← hE] at h_indep







      · sorry
    · sorry -- mpr case





  -- case cut_swap P' x y a b hd =>
  --   apply Iff.intro
  --   · intro 𝒟
  --     cases 𝒟
  --     rename_i 𝒢1 Γ1 Δ1 A1 hd1 hf1 hneq1 ℰ1
  --     generalize heq : 𝒢1 |ₕ Γ1‚ (x ∶ A1) |ₕ Δ1‚ (y ∶ A1ᗮ) = ℋ
  --     rw [heq] at ℰ1
  --     cases ℰ1
  --     rename_i 𝒢2 Γ2 Δ2 A2 hd2 hf2 hneq2 ℰ2


  --     have hms : (Γ2‚ Δ2) ∈ 𝒢1 |ₕ Γ1‚ x ∶ A1 |ₕ Δ1‚ y ∶ A1ᗮ := by
  --       rw [heq]
  --       simp [HyperEnv.merge]

  --     simp only [HyperEnv.merge, Finset.mem_union, Finset.mem_singleton] at hms

  --     cases hms
  --     case inl hinl =>
  --       cases hinl
  --       case inl hin =>
  --       ·
  --         have h : 𝒢1 \ {Γ2‚ Δ2} |ₕ {Γ1‚ Δ1} |ₕ {Γ2‚ Δ2} = 𝒢1 |ₕ {Γ1‚ Δ1} := by
  --           rw [HyperEnv.merge_assoc, HyperEnv.merge_comm (Γ1‚ Δ1), ← HyperEnv.merge_assoc]
  --           simp only [HyperEnv.merge]
  --           rw [Finset.sdiff_union_of_subset]
  --           · simp [hin]

  --         have h1 : 𝒢2 = (𝒢1 \ Γ2‚ Δ2) |ₕ Γ1‚ x ∶ A1 |ₕ Δ1‚ y ∶ A1ᗮ := by
  --           let E := Γ2‚ Δ2

  --           -- FIXME: Check if Finset already has this
  --           have set_cancel {α : Type} [DecidableEq α] (S T : Finset α) (x : α)
  --             (heq : S ∪ {x} = T ∪ {x}) (hnS : x ∉ S) (hnT : x ∉ T) :
  --             S = T := by
  --             rw [← Finset.erase_insert hnS, ← Finset.erase_insert hnT]
  --             simp only [Finset.insert_eq, Finset.union_comm, heq]

  --           have h_decomp : 𝒢1 = 𝒢1 \ E |ₕ E := by
  --             simp only [HyperEnv.merge]
  --             rw [Finset.sdiff_union_of_subset]
  --             · simp [E, hin]

  --           rw [h_decomp] at heq
  --           rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc, HyperEnv.merge_comm {Γ2‚ Δ2} _,
  --             ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc] at heq

  --           have hnL : E ≠ Γ1‚ x ∶ A1 := by
  --             intro h_contra
  --             have hx_in_E : x ∈ E.names := by rw [h_contra]; simp
  --             have hx_in_G1 : x ∈ 𝒢1.names :=
  --               Finset.mem_biUnion.mpr ⟨E, hin, hx_in_E⟩
  --             exact hf1.1 hx_in_G1

  --           have hnR : E ≠ (Δ1‚ y ∶ A1ᗮ) := by
  --             intro h_contra
  --             have hy_in_E : y ∈ E.names := by rw [h_contra]; simp
  --             have hy_in_G1 : y ∈ 𝒢1.names :=
  --               Finset.mem_biUnion.mpr ⟨E, hin, hy_in_E⟩
  --             exact hf1.2.2.2.1 hy_in_G1

  --           have hnRest : E ∉ (𝒢1 \ {E} |ₕ {Γ1‚ x ∶ A1} |ₕ {Δ1‚ y ∶ A1ᗮ}) := by
  --             simp only [HyperEnv.merge, Finset.mem_union, Finset.mem_singleton]
  --             push_neg
  --             refine ⟨⟨Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self _), hnL⟩, hnR⟩

  --           have hn𝒢2 : E ∉ 𝒢2 := by
  --             intro hc
  --             let H_cut := {Γ2‚ a ∶ A2} |ₕ {Δ2‚ b ∶ A2ᗮ}
  --             have h_typing_shaped : ⊢ P' ∷ 𝒢2 |ₕ H_cut := by
  --               rw [HyperEnv.merge_assoc] at ℰ2
  --               exact ℰ2

  --             have h_disj_context : 𝒢2.disjoint H_cut :=
  --               Typing.preserves_disjoint (h := h_typing_shaped)

  --             have h_names_in_cut : (Γ2‚ Δ2).names ⊆ H_cut.names := by
  --               simp [H_cut, HyperEnv.names, Env.names, Env.merge]
  --               intro n hn
  --               simp only [Finset.mem_union, Finset.mem_image] at hn ⊢
  --               rcases hn with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  --               · sorry
  --               · sorry

  --             have h_names_in_G2 : (Γ2‚ Δ2).names ⊆ 𝒢2.names :=
  --               Finset.subset_biUnion_of_mem (fun E => Env.names E) hc

  --             have h_names_empty : (Γ2‚ Δ2).names = ∅ :=
  --               Finset.subset_empty.mp (
  --                 Finset.disjoint_iff_inter_eq_empty.mp h_disj_context ▸
  --                 Finset.subset_inter h_names_in_G2 h_names_in_cut
  --               )



  --             simp [Env.names] at h_names_empty


  --           have h1 : 𝒢2 = (𝒢1 \ {E}) |ₕ {Γ1‚ x ∶ A1} |ₕ {Δ1‚ y ∶ A1ᗮ} := by
  --             apply set_cancel _ _ E heq.symm hn𝒢2 hnRest

  --           exact h1
          -- sorry

      -- case inr hin =>
        -- sorry

    -- · sorry -- mpr


      -- have h1 : 𝒢2 = (𝒢1 \ Γ2‚ Δ2) |ₕ Γ1‚ x ∶ A1 |ₕ Δ1‚ y ∶ A1ᗮ := by sorry

      -- rw [h1, HyperEnv.merge_assoc, HyperEnv.merge_comm, ← HyperEnv.merge_assoc,
      --   ← HyperEnv.merge_assoc] at ℰ2

      -- have h2 : ⊢ 𝑣⸨x, y⸩ P' ∷ {Γ2‚ a ∶ A2} |ₕ {Δ2‚ b ∶ A2ᗮ} |ₕ 𝒢1 \ {Γ2‚ Δ2} |ₕ {Γ1‚ Δ1} := by
      --   apply Typing.cut
      --   · sorry -- Disjointness
      --   · exact hneq1
      --   · exact hd1
      --   · exact ℰ2

      -- rw [HyperEnv.merge_comm, HyperEnv.merge_comm _ (𝒢1 \ {Γ2‚ Δ2}),
      --   ← HyperEnv.merge_assoc, ← HyperEnv.merge_assoc,
      --   HyperEnv.merge_comm (Γ1‚ Δ1) _ ] at h2

      -- have h3 : ⊢ 𝑣⸨a, b⸩ (𝑣⸨x, y⸩ P') ∷ 𝒢1 \ {Γ2‚ Δ2} |ₕ {Γ1‚ Δ1} |ₕ {Γ2‚ Δ2} := by
      --   apply Typing.cut
      --   · sorry -- Disjointness
      --   · exact hneq2
      --   · exact hd2
      --   · exact h2

      -- have h4 : 𝒢1 \ {Γ2‚ Δ2} |ₕ {Γ1‚ Δ1} |ₕ {Γ2‚ Δ2} = 𝒢1 |ₕ {Γ1‚ Δ1} := by
      --   rw [HyperEnv.merge_assoc, HyperEnv.merge_comm (Γ1‚ Δ1), ← HyperEnv.merge_assoc]
      --   simp only [HyperEnv.merge]
      --   rw [Finset.sdiff_union_of_subset]
      --   · sorry -- Missing membership {Γ2‚ Δ2} ∈ 𝒢1 (should be obtainable from heq)

      -- rw [h4] at h3
      -- exact h3
















-- theorem preservation {𝒢 ℋ : HyperEnv} {P Q : Proc} {l : Lbl}
--   (hType : ⊢ P ∷ 𝒢) (hPStep : P -[l]->ₚ Q) (hEStep : 𝒢 -[l]->ₑ ℋ) : ⊢ Q ∷ ℋ := by
