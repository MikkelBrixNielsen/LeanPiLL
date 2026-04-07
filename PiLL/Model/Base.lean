-- import Mathlib.Tactic.Common
-- import Mathlib.Tactic.Basic
-- import Mathlib.Tactic.applyFun
-- import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic
import Mathlib.Order.CompleteLattice.Finset



------------------------------ POLYMORPHIC CLASSES (NOTATION)------------------------------

class HasShiftNames (Subject : Type) where
  shift : Subject → Nat → Nat → Subject

notation:max S:max " ↑ᶜ " d:max ", " c:max => HasShiftNames.shift S d c
notation:max S:max " ↑ᶜ " c:max => HasShiftNames.shift S 0 c
notation:max S:max "⁺ᶜ" => HasShiftNames.shift S 0 1

class HasShiftTypes (Subject : Type) where
  shift : Subject → Nat → Nat → Subject

notation:max S:max " ↑ᵗ " d:max ", " c:max => HasShiftTypes.shift S d c
notation:max S:max " ↑ᵗ " c:max => HasShiftTypes.shift S 0 c
notation:max S:max "⁺ᵗ" => HasShiftTypes.shift S 0 1

class HasSubst (Subject Replacement Target : Type) where
  subst : Subject → Replacement → Target → Subject

notation:max S "{" R " // " T "}" => HasSubst.subst S R T

class HasOpen (Subject Replacement Target : Type) where
  open_ : Subject → Replacement → Target → Subject

notation:max S:max "⸨" T " | " R "⸩" => HasOpen.open_ S R T
notation:max S:max "⸨" R "⸩" => HasOpen.open_ S R 0

class HasClose (Subject Replacement Target : Type) where
  close_ : Subject → Replacement → Target → Subject

notation:max S:max "⟪" T " | " R "⟫" => HasClose.close_ S R T
notation:max S:max "⟪" R "⟫" => HasClose.close_ S R 0

class HasOpenTwo (Subject Replacement_1 Replacement_2 Target : Type) where
  open_ : Subject → Replacement_1 → Replacement_2 → Target → Subject

notation:max S:max "⸨" T " | " R1 ", " R2 "⸩" => HasOpenTwo.open_ S R1 R2 T
notation:max S:max "⸨" R1 ", " R2 "⸩" => HasOpenTwo.open_ S R1 R2 0

class HasCloseTwo (Subject Replacement_1 Replacement_2 Target : Type) where
  close_ : Subject → Replacement_1 → Replacement_2 → Target → Subject

notation:max S:max "⟪" T " | " R1 ", " R2 "⟫" => HasCloseTwo.close_ S R1 R2 T
notation:max S:max "⟪" R1 ", " R2 "⟫" => HasCloseTwo.close_ S R1 R2 0

class HasBracket (Subject Content Result : Type) where
   brack : Subject → Content → Result

class HasParen (Subject Content Result : Type) where
   paren : Subject → Content → Result

notation:80 x"⟦⟧" => HasBracket.brack x ()
notation:80 x"⟦"y"⟧" => HasBracket.brack x y
notation:80 x"⸨⸩" => HasParen.paren x ()
notation:80 x"⸨"y"⸩" => HasParen.paren x y

class HasPerm (α : Type) where
  perm : α → α → Prop

infixr:54 " ~ " => HasPerm.perm

------------------------------- ADDITIONAL FINSET THEOREMS --------------------------------

-- lemma Finset.biUnion_union {α β : Type _} [DecidableEq α] [DecidableEq β]
--   (s t : Finset α) (f : α → Finset β) :
--   (s ∪ t).biUnion f = s.biUnion f ∪ t.biUnion f := by
--   ext b
--   simp [Finset.mem_union]
--   constructor
--   · rintro  ⟨a, h, hb⟩
--     cases h
--     · rename_i ha
--       left ; exact ⟨a, ha, hb⟩
--     rename_i ha
--     · right ; exact ⟨a, ha, hb⟩
--   · intro h
--     cases h
--     · rename_i h'
--       rcases h' with ⟨a, ha, hb⟩
--       exact ⟨a, Or.inl ha, hb⟩
--     · rename_i h'
--       rcases h' with ⟨a, ha, hb⟩
--       exact ⟨a, Or.inr ha, hb⟩

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
