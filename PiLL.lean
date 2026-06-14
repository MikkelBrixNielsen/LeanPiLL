import PiLL.SessionFidelity.SubjectReduction

set_option linter.style.emptyLine false

-- Example 2.1
example {n : Nat} {y : FPName} :
  n ⊢ 𝑣⸨•,•⸩ (($0⟦⟧․𝟘) |ₚ ($1⸨⸩․#y⟦⟧․𝟘) ) ∷ [[y ∶ 1]] := by
  apply Typing.cut (𝒢 := ∅) (Γ := ∅) (A := 1)
    (L := {y})

  intros x hxy z hzy hxz

  simp only [HasOpenTwo.open_, Proc.open, Channel.open,
    zero_add, BEq.rfl, ↓reduceIte, Nat.reduceBEq,
    Bool.false_eq_true, HyperEnv.merge_unitL]
  simp only [Finset.mem_singleton, ← ne_eq] at hzy hxy

  apply Typing.mix (by simp [hxy, hxz])
  · apply Typing.one
    exact Typing.mix₀

  · apply Typing.bot (by simp [hzy])
    apply Typing.one
    exact Typing.mix₀
