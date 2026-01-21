import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- /- Zulip example -/
-- abbrev Env := Finset (Nat × Nat)
-- abbrev HyperEnv := Finset (Env)

-- inductive Typing : HyperEnv → Prop where
--   | parr {Γ : Env} {x y A B : Nat} :
--       Typing {Γ ∪ {(y, A)} ∪ {(x, B)}} →
--       Typing {Γ ∪ {(x, A + B)}}

-- inductive TS1 : HyperEnv → List (Nat × Nat) →
--   HyperEnv → Prop where
--   | parr
--       {Γ : Env} {x y A B : Nat}
--       (𝒟 : Typing {Γ ∪ {(x, A + B)}})
--       (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}}) :
--       TS1
--         {Γ ∪ {(x, A + B)}}
--         [(x, y)]
--         {Γ ∪ {(y, A)} ∪ {(x, B)}}

-- inductive TS2 : ∀ {𝒢 𝒢' : HyperEnv},
--   Typing 𝒢 → List (Nat × Nat) → Typing 𝒢' → Prop where
--   | parr
--       {Γ : Env} {x y A B : Nat}
--       (𝒟 : Typing {Γ ∪ {(y, A)} ∪ {(x, B)}}) :
--       TS2
--         (Typing.parr 𝒟)
--         [(x, y)]
--         𝒟

-- theorem swap_last_two (A B C : Env) : A ∪ B ∪ C = A ∪ C ∪ B := by aesop
-- theorem move_last_two_left (A B C D : Env) : A ∪ B ∪ C ∪ D = A ∪ D ∪ B ∪ C := by aesop

-- theorem example1 {Γ : Env} {x y z A B : Nat}
--   (𝒟 : Typing {Γ ∪ {(x, A + B)} ∪ {(z, 0)}})
--   (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}}) :
--   TS1
--     {Γ ∪ {(x, A + B)} ∪ {(z, 0)}}
--     [(x, y)]
--     {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}} := by
--   rw [move_last_two_left]
--   rw [swap_last_two]
--   apply TS1.parr
--   · rw [← swap_last_two] ; exact 𝒟
--   · rw [← move_last_two_left] ; exact 𝒟'

-- theorem example2 {Γ : Env} {x y z A B : Nat}
--   (𝒟 : Typing {Γ ∪ {(x, A + B)} ∪ {(z, 0)}})
--   (𝒟' : Typing {Γ ∪ {(y, A)} ∪ {(x, B)} ∪ {(z, 0)}}) :
--   TS2
--     𝒟
--     [(x, y)]
--     𝒟' := by
--   rw! [swap_last_two]
--   rw! [move_last_two_left]
--   apply TS2.parr


abbrev Env := Finset (Nat × Nat)
def Env.mk (x y : Nat) : Env := {(x, y)}

abbrev HyperEnv := Finset Env
instance : Coe Env HyperEnv := ⟨fun Γ => ({Γ} : HyperEnv)⟩

inductive Proc : Type where
  | one     (x : Nat) (P : Proc)

inductive Typing : HyperEnv → Proc → Prop where
  | one {P : Proc} {x : Nat} :
      Typing ∅ P →
      Typing (Env.mk x 1) (Proc.one x P)

inductive Lbl : Type
  | one (x : Nat)

inductive EnvStep : HyperEnv → Lbl → HyperEnv → Prop where
  | one {e : HyperEnv} {x : Nat} (h : e = Env.mk x 1) :
      EnvStep e (.one x) ∅

  | res
    {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y : Nat} {l : Lbl} :
    (EnvStep
      (𝒢 ∪ {Γ ∪ Env.mk x 0} ∪ {Δ ∪ Env.mk y 1})
      l
      (𝒢' ∪ {Γ' ∪ Env.mk x 0} ∪ {Δ' ∪ Env.mk y 1})
    )
    →
    (EnvStep
      (𝒢 ∪ {Γ ∪ Δ})
      l
      (𝒢' ∪ {Γ' ∪ Δ'})
    )

inductive ProcStep : Proc → Lbl → Proc → Prop where
  | one {P : Proc} {x : Nat} :
      ProcStep (Proc.one x P) (.one x) P

theorem TypingStep {𝒢 ℋ : HyperEnv} {P Q : Proc} {l : Lbl}
  (hT : Typing 𝒢 P) (hPS : ProcStep P l Q) (hES : EnvStep 𝒢 l ℋ) :
  Typing ℋ Q := by
  induction hPS

  case one P x =>
    cases hT
    generalize h𝒢 : (Env.mk x 1 : HyperEnv) = 𝒢 at hES
    cases hES with try (simp_all ; done)
      | res => sorry
