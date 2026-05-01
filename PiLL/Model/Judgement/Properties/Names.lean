import PiLL.Model.Judgement.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.Processes.Lemmas
import PiLL.Model.Processes.Fresh

lemma Typing_f_eq_names {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → P.f = 𝒢.names := by
  intro h
  induction h
  case mix₀ => simp only [Proc.f_nil, List.empty_eq, HyperEnv.names_nil]
  case mix ih1 ih2 =>
    simp only [Proc.f_par, HyperEnv.names_merge]
    rw [ih1, ih2]
  case one ih | bot ih | oplus₁ ih | oplus₂ ih | bang ih | quest ih | w ih | exists_ ih
    | forall_ ih => simp [Channel.f, ih]
  case cut ℋ Γ Δ P _ _ L _ ih =>
    simp only [Proc.f_cut, HyperEnv.names_merge, HyperEnv.names_cons, Env.names_merge,
      HyperEnv.names_nil, Finset.union_empty]
    have ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh (L ∪ P.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names)
    simp only [Finset.union_assoc, Finset.mem_union, Env.mem_pair_fst_in_names_iff, not_or,
      not_exists, ne_eq, List.append_assoc, List.cons_append, List.nil_append,
      HyperEnv.names_merge, HyperEnv.names_cons, Env.names_distributes,
      Finset.singleton_union, HyperEnv.names_nil, Finset.union_empty,
      Finset.union_insert, Finset.insert_union] at hx hy ih
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have := ih x hx1 y hy1 hneq
    apply_fun (fun s => (s.erase y).erase x) at this
    rw [Finset.erase_insert (by simp [hy3, hneq.symm]), Finset.erase_insert (by simp [hx3]),
      Finset.erase_right_comm, Proc.f_open_two_erase hx2 hy2 hneq] at this
    exact this
  case tensor Γ Δ P x _ _ _ _ L _ ih =>
    simp only [Proc.f_tensor, HyperEnv.names_cons, Env.names_distributes, Env.names_merge,
      Finset.singleton_union, HyperEnv.names_nil, Finset.union_empty, Channel.f]
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names ∪ Δ.names)
    simp only [Finset.union_assoc, Finset.union_singleton, Finset.union_insert,
      Finset.insert_union, Finset.mem_insert, Finset.mem_union, Env.mem_pair_fst_in_names_iff,
      not_or, not_exists, List.cons_append, List.nil_append, HyperEnv.names_cons,
      Env.names_distributes, Finset.singleton_union, HyperEnv.names_nil,
      Finset.union_empty] at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp only [this, Finset.mem_insert, Finset.mem_union, Env.mem_pair_fst_in_names_iff, true_or,
      Finset.insert_eq_of_mem]
  case parr Γ P x _ _ _ _ L _ ih =>
    simp only [Proc.f_parr, HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty, Channel.f]
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp only [Finset.union_assoc, Finset.union_singleton, Finset.union_insert,
    Finset.insert_union, Finset.mem_insert, Finset.mem_union, Env.mem_pair_fst_in_names_iff,
    not_or, not_exists, HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
    HyperEnv.names_nil, Finset.union_empty] at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]
  case c Γ P x _ _ _ L _ ih =>
    simp only [Proc.f_duplicate, HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty, Channel.f]
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp only [Finset.union_assoc, Finset.union_singleton, Finset.union_insert,
      Finset.insert_union, Finset.mem_insert, Finset.mem_union, Env.mem_pair_fst_in_names_iff,
      not_or, not_exists, HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty] at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]
  case amp ihP ihQ =>
    simp only [Proc.f_amp, ihP, HyperEnv.names_cons, Env.names_distributes, Finset.singleton_union,
      HyperEnv.names_nil, Finset.union_empty, Finset.union_insert, ihQ, Finset.union_idempotent,
      Finset.mem_insert, Env.mem_pair_fst_in_names_iff, true_or, Finset.insert_eq_of_mem,
      Channel.f]
  case exchange_env hP ih =>
    simp only [ih, HyperEnv.names_cons, Env.names_eq_of_perm hP]
  case exchange_hyper hP ih =>
    simp only [ih, HyperEnv.names_eq_of_perm hP]
  case ax hneq =>
    simp [Channel.f]
