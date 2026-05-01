import PiLL.Model.Judgement.Basic
import PiLL.Model.Environment.Lemmas
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.Processes.Lemmas

lemma Typing_weakening {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  Typing n P 𝒢 → ∀ d c, Typing (n + c) (P ↑ᵗ d, c) (𝒢 ↑ᵗ d, c) := by
  intro h
  induction h <;> intro d c
  case mix₀ => exact Typing.mix₀
  case mix hD _ _ ihP ihQ =>
    simp only [HyperEnv.shiftTypes_append]
    apply Typing.mix
    · simp only [HyperEnv.disjoint, HyperEnv.shiftTypes_preserves_names] ; exact hD
    · exact ihP d c
    · exact ihQ d c
  case ax hneq hlc =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, Env.shiftTypes_empty,
      HyperEnv.shiftTypes_empty, Types.shift_dual_comm_notation]
    apply Typing.ax
    · exact hneq
    · exact Types.lc_shift hlc
  case one ih =>
    exact Typing.one (ih d c)
  case bot hF _ ih =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, HyperEnv.shiftTypes_empty]
    apply Typing.bot
    · simp only [Env.shiftTypes_preserves_names, hF, not_false_eq_true]
    · exact ih d c
  case cut A _ L _ ih =>
    simp only [HyperEnv.shiftTypes_append, HyperEnv.shiftTypes_cons, Env.shiftTypes_append,
      HyperEnv.shiftTypes_empty] at ⊢ ih
    apply Typing.cut L (A := A ↑ᵗ d, c)
    intro x y hx hy hneq
    specialize ih x y hx hy hneq d c
    simp only [← Types.shift_dual_comm_notation, List.append_assoc,
      List.cons_append, List.nil_append] at ⊢ ih
    rw [Proc.shiftTypes_openCut_comm] at ih
    exact ih
  case tensor hF L _ ih =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, Env.shiftTypes_append,
      HyperEnv.shiftTypes_empty]
    apply Typing.tensor
    · simp only [Env.shiftTypes_preserves_names]
      exact hF
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih
  case parr hF L _ ih =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, HyperEnv.shiftTypes_empty]
    apply Typing.parr
    · rw [Env.shiftTypes_preserves_names]
      exact hF
    · intro y hy
      specialize ih y hy d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih
  case oplus₁ hlc _ ih =>
    apply Typing.oplus₁
    · exact Types.lc_shift hlc
    · exact ih d c
  case oplus₂ hlc _ ih =>
    apply Typing.oplus₂
    · exact Types.lc_shift hlc
    · exact ih d c
  case amp ihP ihQ =>
    exact Typing.amp (ihP d c) (ihQ d c)
  case quest ih =>
    exact Typing.quest (ih d c)
  case bang ih =>
    rw [← Env.shiftTypes_preserves_names]
    apply Typing.bang
    · simp_all only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons,
        HyperEnv.shiftTypes_empty, Env.serverUsable_shiftTypes]
    · exact ih d c
  case w hlc _ ih =>
    apply Typing.w
    · simp_all [Env.mem_pair_fst_in_names_iff]
    · exact Types.lc_shift hlc
    · exact ih d c
  case c hF L _ ih =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, HyperEnv.shiftTypes_empty]
    apply Typing.c
    · rw [Env.shiftTypes_preserves_names]
      exact hF
    · intro x hx
      specialize ih x hx d c
      rw [Proc.shiftTypes_open0_comm] at ih
      exact ih
  case exists_ hlc _ ih =>
    apply Typing.exists_
    · exact Types.lc_shift hlc
    · simp only [HasSubst.subst]
      rw [← Types.shift_subst_0_comm]
      exact ih d c
  case forall_ Γ Q x B n' hTQ ih =>
    simp only [HyperEnv.shiftTypes_cons, Env.shiftTypes_cons, HyperEnv.shiftTypes_empty]
    apply Typing.forall_
    simp only [HasShiftTypes.shift]
    rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc, Env.shiftTypes_comm]
    apply ih
  case exchange_env hP ih =>
    simp only [HyperEnv.shiftTypes_cons]
    apply Typing.exchange_env
    · exact ih d c
    · exact Env.shiftTypes_preserves_perm hP
  case exchange_hyper hP ih =>
    apply Typing.exchange_hyper
    · exact ih d c
    · exact HyperEnv.shiftTypes_preserves_perm hP
