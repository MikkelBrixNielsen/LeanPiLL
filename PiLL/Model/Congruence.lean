import PiLL.Model.Process

-- inductive StructCong : Proc → Proc → Prop where
--   | refl (P : Proc) : StructCong P P
--   | symm {P Q : Proc} : StructCong P Q → StructCong Q P
--   | trans {P Q R : Proc} : StructCong P Q → StructCong Q R → StructCong P R

--   | par_congr {P P' Q : Proc} :
--       StructCong P P' → StructCong (P |ₚ Q) (P' |ₚ Q)
--   | cut_congr {P P' : Proc} {x y : PName} :
--       StructCong P P' → StructCong (𝑣⸨x, y⸩ P) (𝑣⸨x, y⸩ P')

--   | par_comm (P Q : Proc) : StructCong (P |ₚ Q) (Q |ₚ P)
--   | par_assoc (P Q R : Proc) : StructCong ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))
--   | par_zero (P : Proc) : StructCong (P |ₚ 𝟘) P

--   | cut_scope {P Q : Proc} {x y : PName}
--       (hFresh : x ∉ Q.f ∧ y ∉ Q.f) :
--       StructCong ((𝑣⸨x, y⸩ P) |ₚ Q) (𝑣⸨x, y⸩ (P |ₚ Q))
--   | cut_swap {P : Proc} {x y a b : PName}
--       (hDisj : ({x, y} ∩ {a, b} : Finset PName) = ∅) :
--       StructCong (𝑣⸨x, y⸩ (𝑣⸨a, b⸩ P)) (𝑣⸨a, b⸩ (𝑣⸨x, y⸩ P))

-- infix:50 " ≡ₚ " => StructCong

inductive StructCong : Proc → Proc → Prop where
  | refl (P : Proc) : StructCong P P
  | symm {P Q : Proc} : StructCong P Q → StructCong Q P
  | trans {P Q R : Proc} : StructCong P Q → StructCong Q R → StructCong P R
  | par_congr {P P' Q Q' : Proc} :
      StructCong P P' → StructCong Q Q' → StructCong (P |ₚ Q) (P' |ₚ Q')
  | cut_congr {P P' : Proc} :
      StructCong P P' → StructCong (𝑣⸨$N,$N⸩ P) (𝑣⸨$N,$N⸩ P')
  | par_comm (P Q : Proc) : StructCong (P |ₚ Q) (Q |ₚ P)
  | par_assoc (P Q R : Proc) : StructCong ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))
  | par_zero (P : Proc) : StructCong (P |ₚ 𝟘) P
  -- 4. Scope Extrusion
  -- For LN 𝒗⸨#, #⸩ (P | Q) ≡ (𝑣⸨#, #⸩ P) | Q" IF Q doesn't have dangling bound variable
  -- which could risk capturing 0 or 1 from 𝒗⸨#, #⸩. This amounts to checking lcProc Q.
  | cut_scope {P Q : Proc} :
      Proc.lc_0 Q →
      StructCong ((𝑣⸨$N,$N⸩ P) |ₚ Q) (𝑣⸨$N,$N⸩ (P |ₚ Q))

infix:50 " ≡ₚ " => StructCong

-- Note: Cut_swap case currentlæy omitted from above StructCong version due to no index
-- handling / swapping being present for De Bruijn (apparently this seems normal to do?).
