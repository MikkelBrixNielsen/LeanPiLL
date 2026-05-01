import PiLL.Model.Judgement.Basic
import PiLL.Model.Processes.Lemmas
import PiLL.Model.HyperEnvironment.Lemmas.Basic

macro "simp_substTypes" : tactic =>
  `(tactic|
    simp only [
      Proc.substTypes_par, Proc.substTypes_ax, HyperEnv.substTypes_nil, HyperEnv.substTypes_merge,
      HyperEnv.substTypes_distributes, Env.substTypes_nil, Env.substTypes_merge,
      Env.substTypes_distributes, Types.subst_dual_comm_notation, List.empty_eq
    ])

lemma Typing_substTypes {n k : Nat} {P : Proc} {𝒢 : HyperEnv} {A : Types} :
  Typing (n + 1) P 𝒢 → A.lc n → k ≤ n → Typing n (P{A // k}) (𝒢{A // k}) := by
  intro hT hlcA hk
  generalize heq : n + 1 = n' at hT
  induction hT generalizing n A k hk <;> try simp_substTypes
  case mix₀ => exact Typing.mix₀
  case mix hD _ _ ihP ihQ =>
    apply Typing.mix
    · exact HyperEnv.substTypes_preserves_disjoint hD
    · exact ihP hlcA hk heq
    · exact ihQ hlcA hk heq
  case one ih => exact Typing.one (ih hlcA hk heq)
  case bot hF _ ih =>
    apply Typing.bot
    · rw [Env.substTypes_preserves_names]
      exact hF
    · exact ih hlcA hk heq
  case cut 𝒢' Γ Δ Q B n'' L hTP ih =>
    simp only [ne_eq, Proc.openCut_substTypes_comm_notation, List.append_assoc, List.cons_append,
      List.nil_append, HyperEnv.substTypes_merge, HyperEnv.substTypes_distributes,
      Env.substTypes_distributes, Types.subst_dual_comm_notation, HyperEnv.substTypes_nil] at ih
    subst heq
    apply Typing.cut (A := B{A // k}) L
    simp only [ne_eq, HyperEnv.merge, List.append_assoc, List.cons_append, List.nil_append]
    intro x y hx hy hneq
    exact ih x y hx hy hneq (n := n) (k := k) (A := A) hlcA hk (by simp)
  case tensor L _ ih =>
    simp only [Proc.open_substTypes_comm_notation, List.cons_append, List.nil_append,
      HyperEnv.substTypes_distributes, Env.substTypes_distributes, HyperEnv.substTypes_nil] at ih
    apply Typing.tensor (by simp_all) L
    · intro y hy
      exact ih y hy hlcA hk heq
  case parr L _ ih =>
    simp only [Proc.open_substTypes_comm_notation, HyperEnv.substTypes_distributes,
      Env.substTypes_distributes, HyperEnv.substTypes_nil] at ih
    apply Typing.parr ?_ L
    · intro y hy
      exact ih y hy hlcA hk heq
    · simp_all only [Env.mem_pair_fst_in_names_iff, not_exists, Env.substTypes_preserves_names,
        exists_const, not_false_eq_true]
  case oplus₁ hlcB _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.oplus₁
    · exact Types.lc_subst_lc_eq_lc hlcB hlcA hk
    · exact 𝒟
  case oplus₂ hlc _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.oplus₂
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · exact 𝒟
  case amp ihP ihQ => exact Typing.amp (ihP hlcA hk heq) (ihQ hlcA hk heq)
  case quest ih => exact Typing.quest (ih hlcA hk heq)
  case bang his _ ih =>
    rw [← Env.substTypes_preserves_names]
    exact Typing.bang (Env.serverUsable_substTypes his) (ih hlcA hk heq)
  case w hF hlc _ ih =>
    have 𝒟 := ih hlcA hk heq
    subst heq
    apply Typing.w
    · rw [Env.substTypes_preserves_names]
      exact hF
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · exact 𝒟
  case c L _ ih =>
    simp only [Proc.open_substTypes_comm_notation, HyperEnv.substTypes_distributes,
      Env.substTypes_distributes, HyperEnv.substTypes_nil] at ih
    apply Typing.c ?_ L
    · intro x hx
      exact ih x hx hlcA hk heq
    · simp_all only [Env.mem_pair_fst_in_names_iff, not_exists, Env.substTypes_preserves_names,
        exists_const, not_false_eq_true]
  case exists_ hlc _ ih =>
    have := ih hlcA hk heq
    subst heq
    apply Typing.exists_
    · exact Types.lc_subst_lc_eq_lc hlc hlcA hk
    · simp only [HasSubst.subst]
      rw [← Types.subst_comm_0]
      exact this
  case forall_ Γ P x B _ _ ih =>
    simp only [Nat.add_right_cancel_iff, HyperEnv.substTypes_distributes,
      Env.substTypes_distributes, HyperEnv.substTypes_nil] at ih
    have hk' : k + 1 ≤ n + 1 := by grind
    have := ih (Types.lc_shift_0 hlcA) hk' heq
    subst heq
    apply Typing.forall_
    simp only [HasSubst.subst, HasShiftTypes.shift, Env.shiftTypes_substTypes_comm] at ⊢ this
    exact this
  case exchange_env hP ih =>
    simp only [HyperEnv.substTypes_distributes] at ih
    apply Typing.exchange_env
    · exact ih hlcA hk heq
    · exact Env.substTypes_preserves_perm hP
  case exchange_hyper hP ih =>
    apply Typing.exchange_hyper
    · exact ih hlcA hk heq
    · exact HyperEnv.substTypes_preserves_perm hP
  case ax hneq hlcB =>
    subst heq
    apply Typing.ax
    · exact hneq
    · exact Types.lc_subst_lc_eq_lc hlcB hlcA hk
