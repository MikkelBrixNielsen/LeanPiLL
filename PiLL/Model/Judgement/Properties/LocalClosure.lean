import PiLL.Model.Judgement.Basic
import PiLL.Model.Environment.Lemmas
import PiLL.Model.HyperEnvironment.Lemmas.Basic
import PiLL.Model.Processes.lemmas
import PiLL.Model.Processes.Fresh

lemma Typing_preserves_lc_context {𝒢 : HyperEnv} {P : Proc} {n : Nat} :
  (n ⊢ P ∷ 𝒢) → ∀ Γ ∈ 𝒢, Γ.lc n := by
  intro hT E hE𝒢
  induction hT generalizing E
  case mix₀ => simp_all
  case mix =>
    simp only [List.mem_append] at hE𝒢
    cases hE𝒢 <;> simp_all
  case one | bot | quest | bang | amp | oplus₁ | oplus₂ | w | ax =>
    simp_all [Env.lc_cons, Types.lc, Types.lc_dual.mp]
  case exists_ Γ _ x A B n hlc _ ih =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE𝒢
    subst hE𝒢
    have h : Env.lc n ((x, B{A // 0}) :: Γ) := ih ((x, B{A // 0}) :: Γ) (by simp)
    rw [Env.lc_cons] at h ⊢
    exact ⟨(Types.lc_subst_inv_0 hlc).mp h.1, by simp_all⟩
  case forall_ Γ _ x B n _ ih =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE𝒢
    subst hE𝒢
    have h : Env.lc (n + 1) ((x, B) :: Γ⁺) := ih ((x, B) :: Γ⁺) (by simp)
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, implies_true, Env.lc_cons]
    constructor
    · simp [Types.lc, h.1]
    · exact Env.lc_shift_inv_0.mp h.2
  case cut Γ Δ _ A n L _  ih =>
    obtain ⟨u, v, hu, hv, hneq⟩ := exists_two_fresh L
    specialize ih u hu v hv hneq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hE𝒢
    cases hE𝒢 with
    | inl => simp_all
    | inr hin =>
      subst hin
      have hΓ : Env.lc n ((u, A) :: Γ) := ih ((u, A) :: Γ) (by simp)
      have hΔ : Env.lc n ((v, Aᗮ) :: Δ) := ih ((v, Aᗮ) :: Δ) (by simp)
      rw [Env.lc_cons] at hΓ hΔ
      exact Env.lc_append.mpr ⟨hΓ.2, hΔ.2⟩
  case tensor L _ ih | parr L _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [Env.lc_cons]
    simp_all [Types.lc, Env.lc_append]
  case c L _ ih =>
    obtain ⟨u, hu⟩ := exists_one_fresh L
    specialize ih u hu
    simp_all [Env.lc_cons]
  case exchange_env hP ih =>
    simp_all only [List.mem_cons, forall_eq_or_imp]
    cases hE𝒢 with
    | inl => simp_all [(Env.lc_perm hP).mp]
    | inr => simp_all
  case exchange_hyper hP ih =>
    obtain ⟨Ξ, hin𝒢, hPΞ⟩ := HyperEnv.Perm_mem (Γ := E) hP hE𝒢
    exact (Env.lc_perm hPΞ).mp (ih Ξ hin𝒢)

lemma Typing_preserves_lc_proc {𝒢 : HyperEnv} {P : Proc} {n : Nat}
  (hT : n ⊢ P ∷ 𝒢) : P.lc 0 n := by
  induction hT <;> try simp only [Proc.lc, Channel.lc, zero_add, true_and]
  case mix ihP ihQ => exact ⟨ihP, ihQ⟩
  case one ih | bot ih | oplus₁ ih | oplus₂ ih | quest ih | w ih | forall_ ih
    | exchange_env ih | exchange_hyper ih =>
    exact ih
  case bang ih =>
    constructor
    · simp only [Finset.lc, Finset.mem_image, forall_exists_index]
      intros u a ha
      rw [← ha.2]
      simp only [Channel.lc]
    · exact ih
  case cut L _ ih =>
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh L
    exact Proc.lc_of_open_two (ih x hx y hy hneq)
  case amp ihP ihQ =>
    split_ands
    · exact ihP
    · exact ihQ
  case tensor L _ ih | parr L _ ih | c L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh L
    exact Proc.lc_of_open_gen (ih y hy)
  case exists_ hlc _ ih => exact ⟨ih, hlc⟩

lemma Typing_preserves_lc {𝒢 : HyperEnv} {P : Proc} {n : Nat}
  (hT : n ⊢ P ∷ 𝒢) : P.lc 0 n ∧ ∀ Γ ∈ 𝒢, Γ.lc n := by
  constructor
  · exact Typing_preserves_lc_proc hT
  · intro E hE𝒢 ; exact Typing_preserves_lc_context hT E hE𝒢
