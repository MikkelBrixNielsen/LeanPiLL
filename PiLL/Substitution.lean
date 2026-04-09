import PiLL.Model.Judgement

macro "split_names_pos " hxy:ident ", " proof:ident : tactic =>
`(tactic| (
  subst $hxy
  simp at ⊢ $proof
  exact $proof
  ))

macro "split_names_neg " ih:ident ", " huniq:ident : tactic =>
  `(tactic| (
    simp at $ih $huniq
    apply $ih:ident
    intros T h
    rcases h with ⟨hL, hR⟩ | h
    · exact $huniq _ (Or.inl ⟨hL, rfl⟩)
    · exact $huniq _ (Or.inr h)
  ))

macro "split_names_neg_triple " ih:ident ", " huniq:ident ", " hneq:ident : tactic =>
  `(tactic| (
    simp at $ih $huniq
    rw [Proc.open_substNames_comm $hneq, FPName.subst_self_of_ne $hneq] at $ih:ident
    apply $ih:ident
    intros T h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h <;> (
      try exact $huniq _ (Or.inl ⟨h1, rfl⟩)
      try subst h1 h2 ; contradiction
      try exact $huniq _ (Or.inr h)
    )
  ))

macro "split_names " x:term " eq " y:term " using "
  proof:ident ", " ih:ident ", " huniq:ident : tactic =>
  `(tactic| (
    by_cases hxy : $x = $y
    case pos => split_names_pos hxy, $proof
    case neg => split_names_neg $ih, $huniq
  ))

macro "simp_substNames" : tactic =>
  `(tactic|
    simp only [
      Proc.substNames_nil, Proc.substNames_par, Proc.substNames_one, Proc.substNames_bot,
      Proc.substNames_cut, Proc.substNames_tensor, Proc.substNames_parr, Proc.substNames_oplus₁,
      Proc.substNames_oplus₂, Proc.substNames_amp, Proc.substNames_quest, Proc.substNames_bang,
      Proc.substNames_w, Proc.substNames_c, Proc.substNames_exists, Proc.substNames_forall,
      Proc.substNames_ax, Channel.subst_free, HyperEnv.substNames_distributes,
      HyperEnv.substNames_merge, HyperEnv.substNames_of_not_mem, HyperEnv.names_nil,
      Env.substNames_distributes, Env.substNames_merge, Env.substNames_of_not_mem, Env.names_nil,
      List.empty_eq, Finset.notMem_empty, not_false_eq_true
    ])

-- Condition: y is not already in G (unless y = x, which is a no-op)
lemma Typing_substNames {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x y : FPName} :
  Typing n P 𝒢 → (∀ Γ ∈ 𝒢, ∀ A, (y, A) ∈ Γ → y = x) →
  Typing n (P{y // x}) (𝒢{y // x}) := by
  intro hT huniq
  induction hT generalizing x y <;> try simp_substNames
  case mix₀ => exact Typing.mix₀
  case mix hD _ _ ihP ihQ =>
    apply Typing.mix
    · apply HyperEnv.substNames_preserves_disjoint
      · exact hD
      · exact huniq
    · apply ihP
      intros Γ hin𝒢 T hinΓ
      exact huniq Γ (by simp only [List.mem_append]; apply Or.inl hin𝒢) T hinΓ
    · apply ihQ
      intros Γ hin𝒢 T hinΓ
      exact huniq Γ (by simp only [List.mem_append] ; apply Or.inr hin𝒢) T hinΓ
  case one ih =>
    apply Typing.one (ih ?_)
    simp only [List.empty_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  case bot hF _ ih =>
    apply Typing.bot
    · exact Env.fresh_substNames hF huniq
    · apply ih
      intros Γ hΓ T hinΓ
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Prod.mk.injEq] at huniq hΓ
      subst hΓ
      exact huniq T (Or.inr hinΓ)
  case cut Γ Δ _ A _ L _ ih =>
    apply Typing.cut (A := A) (L ∪ {x} ∪ {y})
    intros z w hz hw hneq
    simp only [Finset.union_singleton, Finset.mem_insert, not_or] at hz hw
    obtain ⟨hz1, hz2, hz3⟩ := hz
    obtain ⟨hw1, hw2, hw3⟩ := hw
    specialize ih z w hz3 hw3 hneq
    · exact x
    · exact y
    · by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg =>
        simp only [HyperEnv.merge, List.append_assoc, List.cons_append, List.nil_append,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, HyperEnv.substNames_merge,
            HyperEnv.substNames_distributes, Env.substNames_distributes, HyperEnv.names_nil,
            Finset.notMem_empty, not_false_eq_true, HyperEnv.substNames_of_not_mem] at ⊢ ih huniq
        rw [FPName.subst_self_of_ne hz2, FPName.subst_self_of_ne hw2,
          Proc.openCut_substNames_comm hz2 hw2] at ih
        apply ih
        intro Ξ h T hinΞ
        cases h with
        | inl hL => exact huniq Ξ (Or.inl hL) T hinΞ
        | inr hR =>
          simp only at hR
          rcases hR with rfl | rfl
          all_goals
            simp only [List.mem_cons, Prod.mk.injEq] at hinΞ
            rcases hinΞ with ⟨rfl, rfl⟩ | h
            · contradiction
            · exact huniq (Γ‚ Δ) (Or.inr rfl) T (by grind)
  case tensor hF L _ ih =>
    apply Typing.tensor (Env.fresh_substNames_binary hF huniq) (L ∪ {x} ∪ {y})
    · intros z hz
      simp only [Finset.union_singleton, Finset.mem_insert, not_or] at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      specialize ih z hz3
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg =>
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, Prod.mk.injEq, forall_eq, HyperEnv.substNames_distributes,
          Env.substNames_distributes, HyperEnv.names_nil, Finset.notMem_empty, not_false_eq_true,
          HyperEnv.substNames_of_not_mem, and_imp, List.mem_append] at ⊢ ih huniq
        rw [Proc.open_substNames_comm hz2, FPName.subst_self_of_ne hz2] at ih
        apply ih <;> (intros T h ; rcases h with ⟨rfl, rfl⟩ | h)
        · contradiction
        · exact huniq _ (Or.inr (Or.inl h))
        · exact huniq _ (Or.inl ⟨rfl, rfl⟩)
        · exact huniq _ (Or.inr (Or.inr h))
  case parr A B _ hF L _ ih =>
    apply Typing.parr (Env.fresh_substNames hF huniq) (L ∪ {x} ∪ {y})
    · intros z hz
      simp only [Finset.union_singleton, Finset.mem_insert, not_or] at hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      specialize ih z hz3
      · exact x
      · exact y
      by_cases hxy : x = y
      case pos => split_names_pos hxy, ih
      case neg => split_names_neg_triple ih, huniq, hz2
  case oplus₁ hlc hT ih =>
    apply Typing.oplus₁
    · exact hlc
    · split_names x eq y using hT, ih, huniq
  case oplus₂ A _ _ hlc hT ih =>
    apply Typing.oplus₂
    · exact hlc
    · split_names x eq y using hT, ih, huniq
  case amp A B _ hTP hTQ ihP ihQ =>
    apply Typing.amp
    · split_names x eq y using hTP, ihP, huniq
    · split_names x eq y using hTQ, ihQ, huniq
  case quest hT ih =>
    apply Typing.quest
    split_names x eq y using hT, ih, huniq
  case bang hServ hT ih =>
    rw [Env.names_substNames_image_free]
    apply Typing.bang
    · exact Env.serverUsable_substNames hServ
    · split_names x eq y using hT, ih, huniq
  case w hF hlc hT ih =>
    apply Typing.w
    · exact Env.fresh_substNames hF huniq
    · exact hlc
    · by_cases hxy : x = y
      case pos => split_names_pos hxy, hT
      case neg =>
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq,
          HyperEnv.substNames_distributes, HyperEnv.names_nil, Finset.notMem_empty,
          not_false_eq_true, HyperEnv.substNames_of_not_mem, Prod.mk.injEq] at ih huniq
        apply ih
        intros T h
        exact huniq T (Or.inr h)
  case c A _ hF L hT ih =>
    apply Typing.c ?_ (L ∪ {x} ∪ {y})
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq,
        HyperEnv.substNames_distributes, HyperEnv.names_nil,Finset.notMem_empty,
        not_false_eq_true, HyperEnv.substNames_of_not_mem, Prod.mk.injEq] at ih huniq
      simp only [Finset.union_singleton, Finset.mem_insert, not_or] at hw
      obtain ⟨hw1, hw2, hw3⟩ := hw
      specialize hT w hw3
      specialize ih w hw3 (x := x) (y := y)
      by_cases hxy : x = y
      case pos => split_names_pos hxy, hT
      case neg => split_names_neg_triple ih, huniq, hw2
    · exact Env.fresh_substNames hF huniq
  case exists_ B _ hlc hT ih =>
    apply Typing.exists_
    · exact hlc
    · split_names x eq y using hT, ih, huniq
  case forall_ ih =>
    apply Typing.forall_
    have := ih (x := x) (y := y)
    rw [Env.shiftTypes_substNames_comm]
    simp only [HyperEnv.substNames_distributes, Env.substNames_distributes,
      HyperEnv.substNames_nil] at this
    apply this
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Prod.mk.injEq] at ⊢ huniq this
    intros T h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact huniq ∀․T (Or.inl ⟨rfl, rfl⟩)
    · have ⟨A, hinΓ, _⟩:= (Env.mem_shiftTypes_iff.mp h)
      exact huniq A (Or.inr hinΓ)
  case exchange_env hP ih =>
    apply Typing.exchange_env
    · apply ih
      intros Γ hΓ T hinΓ
      simp only [List.mem_cons, forall_eq_or_imp] at huniq
      cases hΓ with
      | head => exact huniq.1 T ((List.Perm.mem_iff (a := (y, T)) hP).mp hinΓ)
      | tail _ hin𝒢 => exact huniq.2 Γ hin𝒢 T hinΓ
    · exact Env.substNames_preserves_perm hP
  case exchange_hyper hP ih =>
    apply Typing.exchange_hyper
    · apply ih
      intros Γ hΓ T hinΓ
      obtain ⟨Δ, hΔ, hPΔ⟩ := HyperEnv.Perm_mem hP.symm hΓ
      have hinΔ := (List.Perm.mem_iff hPΔ).mpr hinΓ
      exact huniq Δ hΔ T hinΔ
    · apply HyperEnv.substNames_preserves_perm hP
  case ax A _ hneq hlc =>
    apply Typing.ax
    · apply FPName.subst_preserves_neq
      · exact hneq
      · intro h
        subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Prod.mk.injEq, true_and,
          forall_eq_or_imp, and_imp, forall_eq_apply_imp_iff] at huniq
        exact huniq.1
      · intro h
        subst h
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Prod.mk.injEq,
          true_and] at huniq
        exact huniq A (Or.inr rfl)
    · exact hlc

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
