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

theorem Typing.f_eq_names {P : Proc} {𝒢 : HyperEnv} (h : ⊢ P ∷ 𝒢) :
  P.f = 𝒢.names := by
  exact Finset.Subset.antisymm (Typing.f_subset_names h) (Typing.names_subset_f h)

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

      cases h
      rename_i x y 𝒢 Γ Δ A hd1 hf hneq 𝒟
      generalize heq : (𝒢 |ₕ Γ‚ x ∶ A |ₕ Δ‚ y ∶ Aᗮ) = 𝒢'
      rw [heq] at 𝒟
      cases 𝒟
      rename_i 𝒢' ℋ' hd2 hP hQ
      convert Typing.mix _ hQ using 1
      rotate_left ; rotate_left ; rotate_left
      · apply Typing.cut 𝒢 Γ Δ _ _ _ A
        · sorry
        · simp_all
        · exact hneq
        · exact hd1














  case cut_swap hd => sorry











-- theorem preservation {𝒢 ℋ : HyperEnv} {P Q : Proc} {l : Lbl}
--   (hType : ⊢ P ∷ 𝒢) (hPStep : P -[l]->ₚ Q) (hEStep : 𝒢 -[l]->ₑ ℋ) : ⊢ Q ∷ ℋ := by
