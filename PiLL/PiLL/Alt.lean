import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic

-- abbrev PName := Nat

-- inductive Proc : Type where
--   | tensor  (x y : PName) (P : Proc)
--   | parr    (x y : PName) (P : Proc)
--   | one     (x : PName) (P : Proc)
--   | bot     (x : PName) (P : Proc)
--   | cut     (x y : PName) (P : Proc)
--   | par     (P Q : Proc)
--   | nil
-- deriving DecidableEq

-- abbrev Atom := Nat

-- inductive Types : Type where
--   | atom      (a : Atom)
--   | atomDual  (a : Atom)
--   | tensor    (A B : Types)
--   | parr      (A B : Types)
--   | one
--   | bot
-- deriving DecidableEq

-- abbrev Env := Finset (PName × Types)

-- abbrev HyperEnv := Finset (Env)

-- inductive Act : Type
--   | one     (x : PName)
--   | bot     (x : PName)
--   | tensor  (x y : PName)
--   | parr    (x y : PName)
-- deriving Repr, DecidableEq

-- inductive Lbl : Type
--   | tau
--   | act   (a : Act)
--   | par   (l l' : Act)
-- deriving Repr, DecidableEq

-- theorem swap_last (A B C : Env) : A ∪ B ∪ C = A ∪ C ∪ B := by
--   rw [Finset.union_assoc, Finset.union_comm B C, Finset.union_assoc]

-- theorem move_last_two_forward (A B C D : Env) : ((A ∪ B) ∪ C) ∪ D = ((A ∪ D) ∪ B) ∪ C := by
--   rw [Finset.union_assoc A B C, swap_last, ← Finset.union_assoc]

-- inductive Typing : HyperEnv → Proc → Prop where
--   | bot {Γ : Env} {P : Proc} {x : PName} : -- {A : Types} :
--       Typing {Γ} P →
--       Typing {Γ ∪ {(x, Types.bot)}} (Proc.bot x P)

--   | parr {Γ : Env} {P : Proc} {x y : PName} {A B : Types} :
--       Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} P →
--       Typing {Γ ∪ {(x, A.parr B)}} (Proc.parr x y P)

-- inductive TypingStep : HyperEnv → Proc → Lbl →
--   HyperEnv → Proc → Prop where
--    | bot
--       {Γ : Env} {P : Proc} {x : Nat}
--       (𝒟 : Typing {Γ ∪ {(x, Types.bot)}} (Proc.bot x P))
--       (𝒟' : Typing {Γ} P) :
--       TypingStep
--         {Γ ∪ {(x, Types.bot)}} (Proc.bot x P)
--         (Lbl.act (Act.bot x))
--         {Γ} P

--   | parr
--       {Γ : Env} {P : Proc} {x y : Nat} {A B : Types}
--       (𝒟 : Typing {Γ ∪ {(x, A.parr B)}} (Proc.parr x y P))
--       (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} P) :
--       TypingStep
--         {Γ ∪ {(x, A.parr B)}} (Proc.parr x y P)
--         (Lbl.act (Act.parr x y))
--         {Γ ∪ {(y, A)} ∪ {(x, B)}} P

-- example {Γ : Env} {P : Proc} {x y z : PName} {A B : Types}
--   (𝒟 : Typing {Γ ∪ {(x, A.parr B)} ∪ {(z, Types.bot)}} (Proc.parr x y (Proc.bot z P)))
--   (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, Types.bot)}} (Proc.bot z P)) :
--   TypingStep
--     {Γ ∪ {(x, A.parr B)} ∪ {(z, Types.bot)}} (Proc.parr x y (Proc.bot z P))
--     (Lbl.act (Act.parr x y))
--     {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, Types.bot)}} (Proc.bot z P) := by

--   rw [swap_last, move_last_two_forward]
--   apply TypingStep.parr
--   · rw [← swap_last]
--     exact 𝒟
--   · rw [← move_last_two_forward]
--     exact 𝒟'





/- WIP: Small extension to TypingStep trying to get the execution in example 2.5 to work -/
-- inductive TypingStep_extended : HyperEnv → Proc → Lbl →
--   HyperEnv → Proc → Prop where
--    | bot
--       {Γ : Env} {P : Proc} {x : Nat}
--       (𝒟 : Typing {Γ ∪ {(x, Types.bot)}} (Proc.bot x P))
--       (𝒟' : Typing {Γ} P) :
--       TypingStep_extended
--         {Γ ∪ {(x, Types.bot)}} (Proc.bot x P)
--         (Lbl.act (Act.bot x))
--         {Γ} P

--   | parr
--       {Γ : Env} {P : Proc} {x y : Nat} {A B : Types}
--       (𝒟 : Typing {Γ ∪ {(x, A.parr B)}} (Proc.parr x y P))
--       (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} P) :
--       TypingStep_extended
--         {Γ ∪ {(x, A.parr B)}} (Proc.parr x y P)
--         (Lbl.act (Act.parr x y))
--         {Γ ∪ {(y, A)} ∪ {(x, B)}} P

--   | syn
--       {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {a a' : Act}
--       {𝒟 : Typing 𝒢 P} {𝒟' : Typing 𝒢' P'}
--       {ℰ : Typing ℋ Q} {ℰ' : Typing ℋ' Q'}
--       (h₁ : TypingStep_extended 𝒢 P (Lbl.act a) 𝒢' P')
--       (h₂ : TypingStep_extended ℋ Q (Lbl.act a') ℋ' Q')
--       -- (disj : ((Lbl.par a a').iNames ∩ (Proc.par P Q).fNames) = ∅)
--       :
--       ----------------------------------------------------------------------
--       TypingStep_extended (𝒢 ∪ ℋ) (P.par Q) (Lbl.par a a') (𝒢' ∪ ℋ') (P'.par Q')

--   | tensor
--       {Γ Δ : Env} {P : Proc} {x y : Nat} {A B : Types}
--       {𝒟 : Typing {Γ ∪ Δ ∪ {(x, A.tensor B)}} (Proc.tensor x y P)}
--       {𝒟' : Typing ({Γ ∪ {(y, A)}} ∪ {Δ ∪ {(x, B)}}) P} :
--       TypingStep_extended
--         {Γ ∪ Δ ∪ {(x, A.tensor B)}} (Proc.tensor x y P)
--         (Lbl.act (Act.tensor x y))
--         ({Γ ∪ {(y, A)}} ∪ {Δ ∪ {(x, B)}}) P

/-
  SYN, ⊗, ⅋ part of the tau transition of the execution in example 2.5
  the CUT part is still missing.
-/
-- example {Γ Γ' Δ : Env} {Q R : Proc} {x x' y y' z : PName} {A B A' B' : Types}
--   (𝒟 : Typing
--         ({Γ' ∪ Γ ∪ {(x, A.tensor B)}} ∪ {Δ ∪ {(y, A'.parr B')} ∪ {(z, Types.bot)}})
--         (Proc.par (Proc.tensor x x' Q) (Proc.parr y y' (Proc.bot z R))))
--   (𝒟' : Typing
--         ({Γ' ∪ {(x', A)}} ∪ {Γ ∪ {(x, B)}} ∪ {Δ ∪ {(y', A')} ∪ {(y, B')} ∪ {(z, Types.bot)}})
--         (Proc.par (Q) (Proc.bot z R)))

--   (ℰ : Typing {Γ' ∪ Γ ∪ {(x, A.tensor B)}} (Proc.tensor x x' Q))
--   (ℰ' : Typing ({Γ' ∪ {(x', A)}} ∪ {Γ ∪ {(x, B)}}) Q)
--   (ℱ : Typing {Δ ∪ {(y, A'.parr B')} ∪ {(z, Types.bot)}} (Proc.parr y y' (Proc.bot z R)))
--   (ℱ'' : Typing {Δ ∪ {(y', A')} ∪ {(y, B')} ∪ {(z, Types.bot)}} (Proc.bot z R)) :
--   TypingStep_extended
--     ({Γ' ∪ Γ ∪ {(x, A.tensor B)}} ∪ {Δ ∪ {(y, A'.parr B')} ∪ {(z, Types.bot)}})
--     (Proc.par (Proc.tensor x x' Q) (Proc.parr y y' (Proc.bot z R)))
--     (Lbl.par (Act.tensor x x') (Act.parr y y'))
--     ({Γ' ∪ {(x', A)}} ∪ {Γ ∪ {(x, B)}} ∪ {Δ ∪ {(y', A')} ∪ {(y, B')} ∪ {(z, Types.bot)}})
--     (Proc.par (Q) (Proc.bot z R)) := by
--     apply TypingStep_extended.syn
--     · exact ℰ
--     · exact ℰ'
--     · exact ℱ
--     · exact ℱ''
--     · apply TypingStep_extended.tensor
--       · exact ℰ
--       · exact ℰ'
--     · rw [swap_last, move_last_two_forward]
--       · apply TypingStep_extended.parr
--         · rw [← swap_last]
--           exact ℱ
--         · rw [← move_last_two_forward]
--           exact ℱ''



/- Zulip example -/
abbrev Env := Finset (Nat × Nat)
abbrev HyperEnv := Finset (Env)

inductive Typing : HyperEnv → Prop where
  | parr {Γ : Env} {x y A B : Nat} :
      Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} →
      Typing {Γ ∪ {(x, A + B)}}

inductive TS1 : HyperEnv → List (Nat × Nat) →
  HyperEnv → Prop where
  | parr
      {Γ : Env} {x y A B : Nat}
      (𝒟 : Typing {Γ ∪ {(x, A + B)}})
      (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}}) :
      TS1
        {Γ ∪ {(x, A + B)}}
        [(x, y)]
        {Γ ∪ {(y, A)} ∪ {(x, B)}}

inductive TS2 : ∀ {𝒢 𝒢' : HyperEnv},
  Typing 𝒢 → List (Nat × Nat) → Typing 𝒢' → Prop where
  | parr
      {Γ : Env} {x y A B : Nat}
      (𝒟 : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}}) :
      TS2
        (Typing.parr 𝒟)
        [(x, y)]
        𝒟

theorem swap_last_two (A B C : Env) : A ∪ B ∪ C = A ∪ C ∪ B := by aesop
theorem move_last_two_left (A B C D : Env) : A ∪ B ∪ C ∪ D = A ∪ D ∪ B ∪ C := by aesop

theorem example1 {Γ : Env} {x y z A B : Nat}
  (𝒟 : Typing {Γ ∪ {(x, A + B)} ∪ {(z, 0)}})
  (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}}) :
  TS1
    {Γ ∪ {(x, A + B)} ∪ {(z, 0)}}
    [(x, y)]
    {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}} := by
  rw [move_last_two_left]
  rw [swap_last_two]
  apply TS1.parr
  · rw [← swap_last_two] ; exact 𝒟
  · rw [← move_last_two_left] ; exact 𝒟'

theorem example2 {Γ : Env} {x y z A B : Nat}
  (𝒟 : Typing {Γ ∪ {(x, A + B)} ∪ {(z, 0)}})
  (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}}) :
  TS2
    𝒟
    [(x, y)]
    𝒟' := by
  rw! [swap_last_two]
  rw! [move_last_two_left]
  apply TS2.parr
