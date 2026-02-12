import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic
import Mathlib.Order.CompleteLattice.Finset

------------------------------ POLYMORPHIC CLASSES (NOTATION)------------------------------

class HasShift (Subject Depth Correction : Type) where
  shift : Subject → Depth → Correction → Subject

notation:max S:max " ↑ " d:max ", " c:max => HasShift.shift S d c
notation:max S:max " ↑ " c:max => HasShift.shift S 0 c
notation:max S:max "⁺" => HasShift.shift S 0 1

class HasSubst (Target New Index : Type) where
  subst : Target → New → Index → Target

notation:max Target "{" New " // " Index "}" => HasSubst.subst Target New Index
notation:max Target "{" New " // " "#T}" => HasSubst.subst Target New 0


-- NOTE: Might be irrelevant now
-- class HasBracket (Subject Content Result : Type) where
--    brack : Subject → Content → Result

-- class HasParen (Subject Content Result : Type) where
--    paren : Subject → Content → Result

------------------------------- ADDITIONAL FINSET THEOREMS --------------------------------

lemma Finset.biUnion_union {α β : Type _} [DecidableEq α] [DecidableEq β]
  (s t : Finset α) (f : α → Finset β) :
  (s ∪ t).biUnion f = s.biUnion f ∪ t.biUnion f := by
  ext b
  simp [Finset.mem_union]
  constructor
  · rintro  ⟨a, h, hb⟩
    cases h
    · rename_i ha
      left ; exact ⟨a, ha, hb⟩
    rename_i ha
    · right ; exact ⟨a, ha, hb⟩
  · intro h
    cases h
    · rename_i h'
      rcases h' with ⟨a, ha, hb⟩
      exact ⟨a, Or.inl ha, hb⟩
    · rename_i h'
      rcases h' with ⟨a, ha, hb⟩
      exact ⟨a, Or.inr ha, hb⟩

lemma Finset.not_mem_of_not_mem_sdiff {α : Type*} [DecidableEq α]
  {s : Finset α} {x y : α} (h_diff : x ∉ s \ {y}) (h_neq : x ≠ y) : x ∉ s := by
  simp at h_diff
  tauto

lemma Finset.disjoint_image_substName {α : Type*} [DecidableEq α]
  (s t : Finset α) (x z : α) :
  Disjoint s t → x ∉ s → x ∉ t →
  Disjoint (s.image (fun n => if n = z then x else n))
           (t.image (fun n => if n = z then x else n)) := by
  intro h_disj h_sx h_tx
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  rw [Finset.mem_image] at ha hb
  rcases ha with ⟨a_pre, ha_pre, rfl⟩
  rcases hb with ⟨b_pre, hb_pre, h_eq⟩
  rw [←h_eq]

  split_ifs at * with h_az h_bz
  · rw [h_az] at ha_pre
    rw [h_bz] at hb_pre
    rw [Finset.disjoint_iff_ne] at h_disj
    exfalso
    exact h_disj z ha_pre z hb_pre rfl
  · intro h_contra
    rw [← h_contra] at hb_pre
    contradiction
  · intro h_contra
    rw [h_contra] at ha_pre
    contradiction
  · intro h_contra
    rw [← h_contra] at hb_pre
    rw [Finset.disjoint_iff_ne] at h_disj
    exact h_disj a_pre ha_pre a_pre hb_pre rfl
