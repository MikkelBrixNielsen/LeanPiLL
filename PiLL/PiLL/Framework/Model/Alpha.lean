-- import PiLL.Framework.Model.Process

/-
  Alpha Equivalance becomes structural equality when using De Brujin / LN. Processes
  varying only on bound names will map to the exact same data structure.

  AlphaEq.refl : P = P hold by rfl
  AlphaEq.symm : P = Q → Q = P hold by Eq.symm
  AlphaEq.trans : P = Q, Q = R → P = R hold by Eq.trans
-/

-- abbrev Renaming := PName → PName

-- def rename (ρ : Renaming) : Proc → Proc
--   | .tensor x y P     => .tensor (ρ x) (ρ y) (rename ρ P)
--   | .parr x y P       => .parr (ρ x) (ρ y) (rename ρ P)
--   | .one x P          => .one (ρ x) (rename ρ P)
--   | .bot x P          => .bot (ρ x) (rename ρ P)
--   | .cut x y P        => .cut (ρ x) (ρ y) (rename ρ P)
--   | .par P Q          => .par (rename ρ P) (rename ρ Q)
--   | .nil              => .nil
--   | .selectL x P      => .selectL (ρ x) (rename ρ P)
--   | .selectR x P      => .selectR (ρ x) (rename ρ P)
--   | .amp x P Q      => .amp (ρ x) (rename ρ P) (rename ρ Q)
--   | .output x P A     => .output (ρ x) (rename ρ P) A
--   | .input x P A      => .input (ρ x) (rename ρ P) A
--   | .server x P       => .server (ρ x) (rename ρ P)
--   | .consume x P      => .consume (ρ x) (rename ρ P)
--   | .duplicate x y P  => .duplicate (ρ x) (ρ y) (rename ρ P)
--   | .dispose x P      => .dispose (ρ x) (rename ρ P)
--   | .link x y         => .link (ρ x) (ρ y)

-- def freshName (s : Finset Nat) : PName :=
--   (Finset.fold Nat.max 0 id s) + 1

-- def renameBound old new P := rename (fun curr => if curr = old then new else curr) P

-- def renameBound2 old1 old2 new1 new2 P := renameBound old2 new2 (renameBound old1 new1 P)

-- -- Only bound names should be renamed and free names should match exactly
-- inductive AlphaEq : Proc → Proc → Prop where
--   | nil : AlphaEq .nil .nil

--   | par {P1 Q1 P2 Q2 : Proc} :
--       AlphaEq P1 Q1 → AlphaEq P2 Q2 → AlphaEq (.par P1 P2) (.par Q1 Q2)

--   | one {P Q : Proc} {x x' : PName} : -- Both PNames are free
--       AlphaEq P Q → x = x' → AlphaEq (.one x P) (.one x' Q)

--   | tensor {P Q : Proc} {x y x' y' : PName} -- x, x' are free y, y' are bound
--       (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
--       AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
--       AlphaEq (.tensor x y P) (.tensor x' y' Q)

--   | bot {P Q : Proc} {x x' : PName} : -- Both PNames are free
--       AlphaEq P Q → x = x' → AlphaEq (.bot x P) (.bot x' Q)

--   | parr {P Q : Proc} {x y x' y' : PName} -- x x' are Free, y y' are bound
--       (w : PName) (hFresh : w ∉ P.names ∪ Q.names) :
--         AlphaEq (renameBound y w P) (renameBound y' w Q) → x = x' →
--         AlphaEq (.parr x y P) (.parr x' y' Q)

--   | cut {P Q : Proc} {x y x' y' : PName} -- x y x' y' are all bound
--       (w1 w2 : PName) (hFresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ Q.names ∧ w2 ∉ P.names ∪ Q.names) :
--         AlphaEq (renameBound2 x y w1 w2 P) (renameBound2 x' y' w1 w2 Q) →
--         AlphaEq (.cut x y P) (.cut x' y' Q)

--   | selectL {P Q : Proc} {x x' : PName} :
--       AlphaEq P Q → x = x' → AlphaEq (.selectL x P) (.selectL x' Q)

--   | selectR {P Q : Proc} {x x' : PName} :
--       AlphaEq P Q → x = x' → AlphaEq (.selectR x P) (.selectR x' Q)

--   | amp {P1 Q1 P2 Q2 : Proc} {x x' : PName} :
--       AlphaEq P1 P2 → AlphaEq Q1 Q2 → x = x' → AlphaEq (.amp x P1 Q1) (.amp x' P2 Q2)

--   | output {P Q : Proc} {x x' : PName} {A A' : Types}:
--       AlphaEq P Q → x = x' → A = A' → AlphaEq (.output x P A) (.output x' Q A')

--   | input {P Q : Proc} {x x' : PName} {X X' : TVar} :
--       AlphaEq P Q → x = x' → X = X' → AlphaEq (.input x P X) (.input x' Q X')

--   | server {P Q : Proc} {x x' : PName} :
--       AlphaEq P Q → x = x' → AlphaEq (.server x P) (.server x' Q)

--   | consume {P Q : Proc} {x x' : PName} :
--       AlphaEq P Q → x = x' → AlphaEq (.consume x P) (.consume x' Q)

--   | duplicate {P Q : Proc} {x y x' y' : PName} :
--       AlphaEq P Q → x = x' → y = y' → AlphaEq (.duplicate x y P) (.duplicate x' y' Q)

--   | dispose {P Q : Proc} {x x' : PName} :
--       AlphaEq P Q → x = x' → AlphaEq (.dispose x P) (.dispose x' Q)

--   | link {x y x' y' : PName} :
--       x = x' → y = y' → AlphaEq (.link x y) (.link x' y')

-- notation:60 P " =ₐ " Q => AlphaEq P Q

-- @[simp]
-- def Proc.size : Proc → Nat
-- | .nil => 1
-- | .link _ _ => 1
-- | .par P Q => 1 + P.size + Q.size
-- | .amp _ P Q => 1 + P.size + Q.size
-- | .tensor _ _ P | .parr _ _ P | .one _ P | .bot _ P | .cut _ _ P | .selectL _ P
-- | .selectR _ P | .output _ P _ | .input _ P _ | .server _ P | .consume _ P
-- | .dispose _ P | .duplicate _ _ P => 1 + P.size

-- lemma freshName_is_fresh (s : Finset PName) : freshName s ∉ s := by
--   let m := Finset.fold Nat.max 0 id s
--   have h_max : ∀ n ∈ s, n ≤ m := by
--     intro n hn ; rw [Finset.le_fold_max] ; grind
--   intro h_contra
--   specialize h_max (freshName s) h_contra
--   unfold m freshName at h_max
--   apply Nat.not_succ_le_self (Finset.fold Nat.max 0 id s)
--   exact h_max

-- lemma size_renameBound_eq (old new : PName) (P : Proc) :
--   (renameBound old new P).size = P.size := by
--   induction P
--   case nil | link =>
--     simp [renameBound, Proc.size]
--     apply rfl
--   case one P ih | bot P ih | selectL P ih | selectR P ih | server P ih
--     | consume P ih | duplicate P ih | dispose P ih =>
--     simp [renameBound, rename, Proc.size]
--     unfold renameBound at ih
--     apply ih
--   case input P A ih | output P X ih | tensor P ih | parr P ih | cut P ih =>
--     simp [renameBound, rename, Proc.size]
--     simp [renameBound] at ih
--     rw [ih]
--   case par P Q ihP ihQ | amp P Q ihP ihQ =>
--     simp [renameBound, rename, Proc.size]
--     simp [renameBound] at ihP
--     simp [renameBound] at ihQ
--     rw [ihP, ihQ]

-- @[refl]
-- theorem AlphaEq.refl (P : Proc) : P =ₐ P := by
--   induction h : P.size using Nat.strong_induction_on generalizing P
--   rename_i n ih
--   cases P

--   case nil | link => repeat constructor

--   case par P Q =>
--     constructor
--     · apply ih P.size
--       · rw [← h]
--         simp [Proc.size]
--         omega
--       · rfl
--     · apply ih Q.size
--       · rw [← h]
--         simp [Proc.size]
--       · rfl

--   case tensor x y P | parr x y P =>
--     constructor
--     · simp ; exact freshName_is_fresh P.names
--     · apply ih P.size
--       · rw [← h]
--         simp only [Proc.size]
--         omega
--       · simp [size_renameBound_eq]
--     · rfl

--   case cut x y P =>
--     let w1 := freshName P.names
--     let w2 := freshName (P.names ∪ {w1})
--     have h_fresh : w1 ≠ w2 ∧ w1 ∉ P.names ∪ P.names ∧ w2 ∉ P.names ∪ P.names := by
--       constructor
--       · intro h_eq ; unfold w1 at h_eq ; unfold w2 at h_eq
--         exact absurd (freshName_is_fresh (P.names ∪ {w1})) (by grind)
--       · simp
--         apply And.intro
--         · exact freshName_is_fresh P.names
--         · unfold w2 w1
--           · intro h_contra
--             apply freshName_is_fresh (P.names ∪ {freshName P.names})
--             apply Finset.mem_union_left
--             exact h_contra
--     apply AlphaEq.cut
--     · exact h_fresh
--     · apply ih P.size
--       · rw [← h]
--         simp [Proc.size]
--       · unfold renameBound2
--         simp [size_renameBound_eq]

--   case one _ P | bot _ P | selectL _ P | selectR _ P | server _ P | dispose _ P
--     | consume _ P | duplicate _ _ P | output _ P _ | input _ P _ =>
--     constructor
--     · apply ih P.size
--       · rw [← h]
--         simp [Proc.size]
--       · rfl
--     repeat rfl

--   case amp _ P Q =>
--     apply AlphaEq.amp
--     · apply ih P.size
--       · rw [← h]
--         simp [Proc.size]
--         omega
--       · rfl
--     · apply ih Q.size
--       · rw [← h]
--         simp [Proc.size]
--       · rfl
--     · rfl

-- lemma AlphaEq.symm (P Q : Proc) (h : P =ₐ Q) : (Q =ₐ P) := by
--   induction h
--   case nil => rfl
--   case one | bot | par | selectL | selectR | amp | output | input | server
--     | consume | duplicate | dispose | link => constructor ; repeat simp [*]

--   case tensor _ _ _ _ _ _ _ hwnPQ _ hxxp hrbQP
--     | parr tensor _ _ _ _ _ _ hwnPQ _ hxxp hrbQP =>
--     constructor
--     · rw [Finset.union_comm] ; exact hwnPQ
--     · exact hrbQP
--     · rw [Eq.comm] ; exact hxxp

--   case cut _ _ _ _ _ _ _ _ h_fresh hrbPQ hrbQP =>
--     constructor
--     · rw [Finset.union_comm] ; exact h_fresh
--     · exact hrbQP

-- theorem AlphaEq.comm (P Q : Proc) : (P =ₐ Q) = (Q =ₐ P) := by
--   apply propext
--   constructor
--   · apply AlphaEq.symm
--   · apply AlphaEq.symm

-- lemma renameBound_comm {x y a b : PName} {P : Proc} :
--   (hxy : x ≠ y) → (hab : a ≠ b) → (hxb : x ≠ b) → (hya : y ≠ a) →
--   renameBound x a (renameBound y b P) = renameBound y b (renameBound x a P) := by
--   intros
--   induction P <;> simp [renameBound, rename, *]
--   case one ih | bot ih | selectL ih | selectR ih | output ih | input ih
--     | server ih | consume ih | dispose ih =>
--     apply And.intro
--     · aesop
--     · exact ih

--   case par P_ih Q_ih =>
--     apply And.intro
--     · exact P_ih
--     · exact Q_ih

--   case amp P_ih Q_ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · exact P_ih
--       · exact Q_ih

--   case link =>
--     apply And.intro
--     · aesop
--     · aesop

--   case tensor ih | parr ih | cut ih | duplicate ih =>
--     apply And.intro
--     · aesop
--     · apply And.intro
--       · aesop
--       · exact ih

-- lemma renameBound_commutes (a b : PName) (P : Proc) (ha : a ∉ P.names) (hb : b ∉ P.names) :
--   renameBound a b P = P := by
--   induction P generalizing a b
--   all_goals simp [rename, renameBound, *]

--   case tensor x y P ih | parr x y P ih | cut x y P ih | duplicate x y P ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · intro h ; simp_all
--       · apply ih <;> simp_all

--   case one x P ih | bot x P ih | selectL x P ih | selectR x P ih | server x P ih
--     | consume x P ih | dispose x P ih | output x P A ih | input x P X ih =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply ih <;> simp_all

--   case amp x P Q ihP ihQ =>
--     apply And.intro
--     · intro h ; simp_all
--     · apply And.intro
--       · apply ihP <;> simp_all
--       · apply ihQ <;> simp_all

--   case par P Q ihP ihQ =>
--     apply And.intro
--     · apply ihP <;> simp_all
--     · apply ihQ <;> simp_all

--   case link =>
--     apply And.intro
--     · intro h ; simp_all
--     · intro h ; simp_all


-- lemma renameBound_comp (x y z : PName) (P : Proc) (hx : x ∉ P.names) (hxy : x ≠ y) :
--   renameBound x z (renameBound y x P) = renameBound y z P := by
--   induction P generalizing x y z <;> simp [renameBound, rename, *] at *
--   all_goals aesop

-- lemma AlphaEq_swap_fresh (y y' w1 w2 : PName) (P Q : Proc)
--   (hFresh1 : w1 ∉ P.names ∪ Q.names)
--   (hFresh2 : w2 ∉ P.names ∪ Q.names)
--   (h : renameBound y w1 P =ₐ renameBound y' w1 Q) :
--   (renameBound y w2 P =ₐ renameBound y' w2 Q) := by sorry

-- theorem AlphaEq.trans (P Q R : Proc) (hPQ : P =ₐ Q) (hQR : Q =ₐ R) : P =ₐ R := by sorry
--   induction P.size + Q.size using Nat.strong_induction_on generalizing P Q R
--   rename_i n ih
--   cases hPQ <;> cases hQR
--   case nil.nil => rfl
--   case par.par =>
--     rename_i P1 Q1 P2 Q2 h1 h2 Q1' Q2' h5 h6
--     apply AlphaEq.par
--     · sorry
