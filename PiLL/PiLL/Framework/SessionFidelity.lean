import PiLL.Framework.Semantics.EnvStep
import PiLL.Framework.Semantics.ProcStep
import PiLL.Framework.Substitution














-- FIXME: Move to Proc
@[simp] lemma Proc.f_nil :
  𝟘.f = ∅ := by simp [Proc.f]

@[simp] lemma Proc.f_one {P : Proc} {u : Channel} :
  (u⟦⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_bot {P : Proc} {u : Channel} :
  (u⸨⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_tensor {P : Proc} {u : Channel} :
  (u⟦$N⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_parr {P : Proc} {u : Channel} :
  (u⸨$N⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_cut {P : Proc} :
  (𝑣⸨$N,$N⸩ P).f = P.f := by simp [Proc.f]

@[simp] lemma Proc.f_par {P Q : Proc} :
   (P |ₚ Q).f = P.f ∪ Q.f := by simp [Proc.f]

@[simp] lemma Proc.f_selectL {P : Proc} {u : Channel} :
  (u⟦𝐋⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_selectR {P : Proc} {u : Channel} :
  (u⟦𝐑⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_amp {P Q : Proc} {u : Channel} :
  (u․case{𝐋 : P, 𝐑 : Q}).f = u.f ∪ P.f ∪ Q.f := by simp [Proc.f]

@[simp] lemma Proc.f_output {P : Proc} {u : Channel} {A : Types} :
  (u⟦A⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_input {P : Proc} {u : Channel} :
  (u⸨$T⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_server {P : Proc} {u : Channel} :
  (!u․{P}).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_consume {P : Proc} {u : Channel} :
  (u⟦USE⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_duplicate {P : Proc} {u : Channel} :
  (u⟦DUP⟧⸨$N⸩․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_dispose {P : Proc} {u : Channel} :
  (u⟦DISP⟧․P).f = u.f ∪ P.f := by simp [Proc.f]

@[simp] lemma Proc.f_link {u v : Channel} :
  (u⟷ₚv).f = u.f ∪ v.f := by simp [Proc.f]


@[simp] lemma Channel.f_open_erase {k : Nat} {u : Channel} {y : FPName} (hy : y ∉ u.f) :
  (u⸨k | #y⸩).f.erase y = u.f := by
  cases u with
  | bound =>
    simp [HasOpen.open_, Channel.open, Channel.f]
    split_ifs <;> simp
  | free z =>
    simp [HasOpen.open_, Channel.open, Channel.f] at ⊢ hy
    exact hy

@[simp] lemma Proc.f_open_erase {P : Proc} {y : FPName} {k : Nat} (hy : y ∉ P.f) :
  (P⸨k | #y⸩.f).erase y = P.f := by
  induction P generalizing k <;> simp [Finset.erase_union_distrib] at ⊢ hy

  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | server ih | consume ih | duplicate ih | dispose ih =>
    rw [Channel.f_open_erase hy.1, ih hy.2]

  case cut ih => exact ih hy
  case par ihP ihQ => rw [ihP hy.1, ihQ hy.2]
  case amp ihP ihQ => rw [Channel.f_open_erase hy.1, ihP hy.2.1, ihQ hy.2.2]
  case link => rw [Channel.f_open_erase hy.1, Channel.f_open_erase hy.2]

@[simp] lemma Proc.f_open_two_erase {P : Proc} {x y : FPName} {k : Nat}
  (hx : x ∉ P.f) (hy : y ∉ P.f) (hneq : x ≠ y) :
  ((P⸨k | #x, #y⸩.f).erase x).erase y = P.f := by
  simp [HasOpenTwo.open_]
  change (P⸨k + 1 | #y⸩⸨k | #x⸩.f.erase x).erase y = P.f
  rw [Proc.f_open_erase, Proc.f_open_erase hy]
  intro h
  have h1 : (P⸨k + 1 | #y⸩.f).erase y = P.f := Proc.f_open_erase hy
  have h2 := Finset.mem_erase_of_ne_of_mem hneq h
  rw [h1] at h2
  contradiction











-- FIXME: Move to Judgement
lemma Typing.f_eq_names {n : Nat} {P : Proc} {𝒢 : HyperEnv} :
  (n ⊢ P ∷ 𝒢) → P.f = 𝒢.names := by
  intro h
  induction h <;> try simp [Channel.f]

  case mix ih1 ih2 => rw [ih1, ih2]

  case one ih | bot ih | oplus₁ ih | oplus₂ ih | quest ih | bang ih | w ih | exists_ ih
    | forall_ ih =>
    simp [ih]

  case cut ℋ Γ Δ P _ _ L _ ih =>
    have ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh (L ∪ P.f ∪ ℋ.names ∪ Γ.names ∪ Δ.names)
    simp at hx hy ih
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have := ih x y hx1 hy1 hneq
    apply_fun (fun s => (s.erase y).erase x) at this
    rw [Finset.erase_insert (by simp [hy3, hneq.symm]), Finset.erase_insert (by simp [hx3]),
      Finset.erase_right_comm, Proc.f_open_two_erase hx2 hy2 hneq] at this
    exact this

  case tensor Γ Δ P x _ _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names ∪ Δ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case parr Γ P x _ _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.insert_comm,
      Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case c Γ P x _ _ _ L _ ih =>
    obtain ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
    simp at hy ih
    obtain ⟨hneq, hy1, hy2, hy3⟩ := hy
    have := ih y hy1
    apply_fun (fun s => s.erase y) at this
    rw [Proc.f_open_erase hy2, Finset.erase_insert (by simp [hneq, hy3])] at this
    simp [this]

  case amp ihP ihQ => simp [ihP, ihQ]

  case exchange_env hP ih =>
    simp [ih, Env.names_eq_of_perm hP]

  case exchange_hyper hP ih =>
    simp [ih, HyperEnv.names_eq_of_perm hP]

@[simp] lemma Env.swap_two {x y : FPName} {A B : Types} :
  [x ∶ A, y ∶ B] ~ [y ∶ B, x ∶ A] := by
  exact List.Perm.swap ..


-- FIXME: use this (HyperEnv.Perm.trans hP HyperEnv.swap_two_inner) for comm?
@[simp] lemma HyperEnv.swap_two_inner {x y : FPName} {A B : Types} :
  [[x ∶ A, y ∶ B]] ~ [[y ∶ B, x ∶ A]] := by
  exact HyperEnv.Perm.cons Env.swap_two HyperEnv.Perm.nil

@[simp] lemma HyperEnv.disjoint_split {𝒢 ℋ : HyperEnv} (hD : (𝒢 |ₕ ℋ).PairwiseDisjoint) :
  𝒢.disjoint ℋ := by
  rw [HyperEnv.disjoint, Finset.disjoint_left]
  rw [HyperEnv.PairwiseDisjoint, HyperEnv.merge, List.pairwise_append] at hD
  intro n hin𝒢 hinℋ
  rw [HyperEnv.mem_pair_fst_in_names] at hin𝒢 hinℋ
  obtain ⟨T1, Γ, hinΓ, hΓ𝒢⟩ := hin𝒢
  obtain ⟨T2, Δ, hinΔ, hΔℋ⟩ := hinℋ
  obtain ⟨h1, h2, h3⟩ := hD
  have := h3 Γ hΓ𝒢 Δ hΔℋ
  simp [Env.disjoint] at this
  have hnΓ := Env.mem_pair_fst_in_names T1 hinΓ
  have hnΔ := Env.mem_pair_fst_in_names T2 hinΔ
  rw [Finset.disjoint_left] at this
  exact this hnΓ hnΔ





lemma Typing_inv_one {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⟦⟧․P) 𝒢) :
  (𝒢 ~ [[x ∶ 1]]) ∧ Typing n P ∅ := by
  generalize heq : (#x⟦⟧․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨h1, h2⟩ := ih heq
    have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
    exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨h1, h2⟩ := ih heq
    exact ⟨HyperEnv.Perm.trans hP.symm h1, h2⟩

  case one hT _ =>
    simp at heq
    constructor
    · simp [heq.1, HasPerm.perm]
    · simp [heq.2]
      exact hT

lemma Typing_inv_bot {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⸨⸩․P) 𝒢) :
  ∃ Γ, (𝒢 ~ [x ∶ ⊥ :: Γ]) ∧ Typing n P [Γ] := by
  generalize heq : (#x⸨⸩․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨Ξ, h⟩ := ih heq
    obtain ⟨h1, h2⟩ := h
    constructor
    · have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
      exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨Γ, h⟩ := ih heq
    obtain ⟨h1, h2⟩ := h
    constructor
    · exact ⟨HyperEnv.Perm.trans hP.symm h1, h2⟩

  case bot hT _ =>
    simp at heq
    constructor
    · constructor
      · simp [heq.1]
        apply HyperEnv.Perm.refl
      · simp [heq.2]
        exact hT

lemma Typing_inv_tensor {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⟦$N⟧․P) 𝒢) :
  ∃ (A B : Types) (Γ Δ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⨂ B :: Γ‚ Δ]) ∧ (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) := by
  generalize heq : (#x⟦$N⟧․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, Δ, L
    constructor
    · exact (HyperEnv.Perm.trans (hP'.symm) (HyperEnv.Perm.cons hP (HyperEnv.Perm.refl _))).symm
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, Δ, L
    constructor
    · exact HyperEnv.Perm.trans (hP.symm) hP'
    · exact hT'

  case tensor Γ Δ Q _ A B _ _ L hT ih =>
    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ Γ.names ∪ Δ.names ∪ Q.f ∪ {x})
    simp at hz heq
    obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hz
    use A, B, Γ, Δ, L
    constructor
    · rw [heq.1]
    · rw [heq.1, heq.2]
      exact hT

lemma Typing_inv_parr {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⸨$N⸩․P) 𝒢) :
  ∃ (A B : Types) (Γ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⅋ B :: Γ]) ∧ (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: x ∶ B :: Γ])) := by
  generalize heq : (#x⸨$N⸩․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, B, Γ, L, hP', hT'⟩:= ih heq
    use A, B, Γ, L
    constructor
    · exact (HyperEnv.Perm.trans (hP'.symm) (HyperEnv.Perm.cons hP (HyperEnv.Perm.refl _))).symm
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨A, B, Γ, L, hP', hT'⟩ := ih heq
    use A, B, Γ, L
    constructor
    · exact HyperEnv.Perm.trans (hP.symm) hP'
    · exact hT'

  case parr Γ Q y A B hF n L hT ih =>
    obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ Γ.names ∪ Q.f ∪ {x})
    simp at hz heq
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    use A, B, Γ, L
    constructor
    · rw [heq.1]
    · rw [heq.1, heq.2]
      exact hT

lemma Typing_inv_par {n : Nat} {P Q : Proc} {𝒢 : HyperEnv} (hT : n ⊢ P |ₚ Q ∷ 𝒢) :
  ∃ 𝒢₁ 𝒢₂, (𝒢 ~ 𝒢₁ |ₕ 𝒢₂) ∧ (n ⊢ P ∷ 𝒢₁) ∧ (n ⊢ Q ∷ 𝒢₂) := by
  generalize heq : (P |ₚ Q) = PQ at hT
  induction hT generalizing P Q <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨ℋ₁, ℋ₂, hP', hT'⟩ := ih heq
    use ℋ₁, ℋ₂
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨ℋ₁, ℋ₂, hP', hT'⟩ := ih heq
    use ℋ₁, ℋ₂
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case mix 𝒢 ℋ _ _ hD _ hTP hTQ ihP ihQ =>
    simp at heq
    obtain ⟨hP, hQ⟩ := heq
    use 𝒢, ℋ
    rw [hP, hQ]
    exact ⟨by simp, ⟨hTP, hTQ⟩⟩

lemma Typing_inv_link {n : Nat} {x y : FPName} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟷ₚ#y ∷ 𝒢) :
  ∃ A, 𝒢 ~ [x ∶ Aᗮ :: [y ∶ A]] := by
  generalize heq : (#x⟷ₚ#y) = P at hT
  induction hT generalizing x y <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨T, hP'⟩ := ih heq
    use T
    exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm HyperEnv.Perm.rfl) hP'

  case exchange_hyper hP ih =>
    obtain ⟨T, hP'⟩ := ih heq
    use T
    exact HyperEnv.Perm.trans hP.symm hP'

  case ax A _ hneq hlc =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use A

lemma Typing_inv_amp {n : Nat} {x : FPName} {P Q : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x․case{𝐋 : P, 𝐑 : Q} ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A & B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) ∧ (n ⊢ Q ∷ [x ∶ B :: Γ]) := by
  generalize heq : (#x․case{𝐋 : P, 𝐑 : Q}) = PQ at hT
  induction hT generalizing P Q x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨𝒢', A, B, hP', hT'⟩ := ih heq
    use 𝒢', A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨𝒢', A, B, hP', hT'⟩ := ih heq
    use 𝒢', A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case amp Γ _ _ x A B _ hTP hTQ ihP ihQ =>
    simp at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_selectL {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦𝐋⟧․P ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A ⊕ B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) := by
  generalize heq : (#x⟦𝐋⟧․P) = PsL at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case oplus₁ Γ _ _ A B  _ hlc hPT ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_selectR {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦𝐑⟧․P ∷ 𝒢) :
  ∃ Γ A B, (𝒢 ~ [x ∶ A ⊕ B :: Γ]) ∧ (n ⊢ P ∷ [x ∶ B :: Γ]) := by
  generalize heq : (#x⟦𝐑⟧․P) = PsR at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, B, hP', hT'⟩ := ih heq
    use Γ, A, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case oplus₂ Γ _ _ A B  _ hlc hPT ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, B

lemma Typing_inv_output {n : Nat} {x : FPName} {A : Types} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦A⟧․P ∷ 𝒢) :
  ∃ Γ B,
  (𝒢 ~ [x ∶ ∃․B :: Γ]) ∧ n ⊢ P ∷ [x ∶ B{A // 0} :: Γ] := by
  generalize heq : (#x⟦A⟧․P) = Pout at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case exists_ Γ _ _ _ B _ hlc hT ih =>
    simp at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    use Γ, B

lemma Typing_inv_input {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⸨$T⸩․P ∷ 𝒢) :
  ∃ (Γ : Env) (B : Types),
  (𝒢 ~ [x ∶ ∀․B :: Γ]) ∧ (n + 1 ⊢ P ∷ [x ∶ B :: Γ⁺ᵗ]) := by
  generalize heq : (#x⸨$T⸩․P) = Pin at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, B, hP', hT'⟩ := ih heq
    use Γ, B
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case forall_ Γ _ _ B _ _ ih  =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, B

lemma Typing_inv_use₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦USE⟧․P ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ ??A :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) := by
  generalize heq : (#x⟦USE⟧․P) = Puse at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env 𝒢 _ _ _ _ _ hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl 𝒢)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case quest Γ _ _ A _ _ ih =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_use₂ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ !#x․{P} ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ !!A :: Γ]) ∧ (n ⊢ P ∷ [x ∶ A :: Γ]) ∧ ?ₑΓ := by
  generalize heq : (!#x․{P}) = Puse at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env 𝒢 _ _ _ _ _ hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl 𝒢)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case bang Γ _ _ A _ _ _ _ =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_disp₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦DISP⟧․P ∷ 𝒢) :
  ∃ Γ A, (𝒢 ~ [x ∶ ??A :: Γ]) ∧ (n ⊢ P ∷ [Γ]) ∧ x ∉ Env.names Γ := by
  generalize heq : (#x⟦DISP⟧․P) = Pdisp at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, hP', hT'⟩ := ih heq
    use Γ, A
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case w Γ _ _ A _ _ _ _ _ =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A

lemma Typing_inv_dup₁ {n : Nat} {x : FPName} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ #x⟦DUP⟧⸨$N⸩․P ∷ 𝒢) :
  ∃ (Γ : Env) (A : Types) (L : Finset FPName),
    (𝒢 ~ [x ∶ ??A :: Γ]) ∧ x ∉ Γ.names ∧
    (∀ x' ∉ L, x' ≠ x → n ⊢ P⸨#x'⸩ ∷ [x' ∶ ??A :: x ∶ ??A :: Γ]) := by
  generalize heq : (#x⟦DUP⟧⸨$N⸩․P) = Pdup at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, x', hP', hT'⟩ := ih heq
    use Γ, A, x'
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl _)) hP'
    · exact hT'

  case exchange_hyper hP ih =>
    obtain ⟨Γ, A, x', hP', hT'⟩ := ih heq
    use Γ, A, x'
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · exact hT'

  case c Γ _ _ A _ hF L hT _ =>
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, L
    constructor
    · simp
    · constructor
      · exact hF
      · intros x' hin hneq
        apply Typing.exchange_hyper (hT x' hin)
        exact HyperEnv.Perm.cons (List.Perm.swap (x' ∶ ??A) (x ∶ ??A) Γ) (by simp)


lemma Typing_buildDisp {n : Nat} {x : FPName} (Γ : Env) (names : List FPName)
  (hServ : ?ₑΓ) (hNodup : names.Nodup) (heq : Γ.names = names.toFinset)
  (hxΓ : x ∉ Γ.names) (hlc : Γ.lc n) (hNodupΓ : Env.Nodup Γ)
  : n ⊢ buildDisp names x ∷ [x ∶ 1 :: Γ] := by
  induction names generalizing Γ

  case nil =>
    rw [Env.names_empty_nil heq]
    exact Typing.one Typing.mix₀

  case cons z zs ih =>
    simp [buildDisp]
    have hzΓ: z ∈ Γ.names := by simp_all
    obtain ⟨A, Γ', hP, hServ', hNames'⟩ := Env.extract_exp hzΓ hServ hNodupΓ
    obtain ⟨hlcB, hlcΓ'⟩ := (Env.lc_cons.mp ((Env.lc_perm hP).mp hlc))
    have hPMap : (Γ.map Prod.fst).Perm (z :: (Γ'.map Prod.fst)) := List.Perm.map _ hP
    have hNodupCons : (z :: (Γ'.map Prod.fst)).Nodup := (List.Perm.nodup_iff hPMap).mp hNodupΓ
    have hNodupΓ' : Env.Nodup Γ' := (List.nodup_cons.mp hNodupCons).2
    apply Typing.exchange_hyper (𝒢 := [z ∶ ??A :: x ∶ 1 :: Γ'])
    · apply Typing.w
      · simp_all
        have : x ≠ z := (hxΓ.1)
        exact this.symm
      · exact hlcB
      · apply ih
        · exact hServ'
        · simp at hNodup
          exact hNodup.2
        · rw [heq] at hNames'
          rw [← Finset.erase_eq] at hNames'
          simp_all
        · simp_all
        · exact hlcΓ'
        · exact hNodupΓ'
    · apply HyperEnv.Perm.cons
      · simp [HasPerm.perm]
        apply List.Perm.trans
        · apply List.Perm.swap
        · apply List.Perm.cons
          exact hP.symm
      · simp

@[simp] lemma Env.serverUsable_nil :
  ?ₑ[] := by simp [Env.serverUsable]

@[simp] lemma Channel.open_bound_zero {x : FPName} :
  ($0)⸨#x⸩ = (#x) := by simp [HasOpen.open_, Channel.open]

@[simp] lemma Channel.f_bound {i : Nat} :
  (Channel.bound i).f = ∅ := by simp [Channel.f]

@[simp] lemma Channel.close_free_self {x : FPName} :
  (#x)⟪x⟫ = (.bound 0) := by simp [HasClose.close_, Channel.close]

@[simp] lemma Channel.close_free_other {x y : FPName} (hneq : x ≠ y) :
  (#y)⟪x⟫ = (#y) := by simp_all [HasClose.close_, Channel.close]

@[simp] lemma Channel.close_self_bound {x : FPName} {i : Nat} :
  (Channel.bound i)⟪x⟫ = (.bound i) := by simp [HasClose.close_, Channel.close]

lemma Channel.close_not_mem {u : Channel} {z : FPName} {k : Nat} (h : z ∉ u.f) :
  u⟪k | z⟫ = u := by
  cases u <;> simp [HasClose.close_, Channel.close, Channel.f] at *
  case free f => apply h

lemma Proc.close_not_mem {P : Proc} {z : FPName} {k : Nat} (h : z ∉ P.f) :
  P⟪k | z⟫ = P := by
  induction P generalizing k <;> (
    simp only [Proc.f, Finset.mem_union, not_or] at h
    try simp
  )
  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
  | server ih | consume ih | dispose ih | duplicate ih => exact ⟨Channel.close_not_mem h.1, ih h.2⟩
  case cut ih => exact ih h
  case par ihP ihQ => exact ⟨ihP h.1, ihQ h.2⟩
  case amp ihP ihQ => exact ⟨Channel.close_not_mem h.1.1, ihP h.1.2, ihQ h.2⟩
  case link => exact ⟨Channel.close_not_mem h.1, Channel.close_not_mem h.2⟩

lemma Proc.closeAll_not_mem {P : Proc} {L : List FPName} {k : Nat}
  (h : P.f = ∅) : closeAll P k L = P := by
  induction L generalizing k P
  case nil => unfold closeAll ; simp
  case cons x Γ ih =>
    unfold closeAll
    rw [Proc.close_not_mem]
    · exact ih h
    · rw [h] ; simp

@[simp] lemma Channel.f_close {u : Channel} {x : FPName} {k : Nat} :
  (u⟪k | x⟫).f = u.f \ {x} := by
  cases u <;> simp [HasClose.close_, Channel.close, Channel.f]
  case free f =>
    split_ifs with heq
    case pos => subst heq ; simp
    case neg =>
      ext y
      simp_all [← ne_eq]
      intro h
      subst h
      exact heq.symm

@[simp] lemma Proc.f_close {P : Proc} {x : FPName} {k : Nat} :
  (P⟪k | x⟫).f = P.f \ {x} := by
  induction P generalizing k <;>
    simp_all [← Finset.erase_eq, Finset.erase_union_distrib]

lemma Channel.lc_le_any {u : Channel} {k i : Nat} (hle : i ≤ k) :
  u.lc i → u.lc k := by
  induction u
  case free => simp [Channel.lc]
  case bound => grind [Channel.lc]

lemma Proc.lc_le_any {P : Proc} {k n i : Nat} (hle : i ≤ k) :
  P.lc i n → P.lc k n := by
  induction P generalizing n k i

  case nil => simp [Proc.lc]

  case one ih | bot ih | selectL ih | selectR ih | input ih | server ih | consume ih
    | dispose ih =>
    simp [Proc.lc]
    intro hChan hProc
    constructor
    · exact Channel.lc_le_any hle hChan
    · exact ih hle hProc

  case tensor ih | parr ih | duplicate ih =>
    simp [Proc.lc]
    intro hChan hProc
    constructor
    · exact Channel.lc_le_any hle hChan
    · exact ih (by simp [hle]) hProc

  case cut ih =>
    simp [Proc.lc] at ⊢ ih
    intro hProc
    apply ih (by simp [hle]) hProc

  case par ihP ihQ =>
    simp [Proc.lc]
    intro hP hQ
    constructor
    · exact ihP hle hP
    · exact ihQ hle hQ

  case amp ihP ihQ =>
    simp [Proc.lc]
    intro hChan hP hQ
    split_ands
    · exact Channel.lc_le_any hle hChan
    · exact ihP hle hP
    · exact ihQ hle hQ

  case output ih =>
    simp [Proc.lc]
    intro hChan hProc hlc
    split_ands
    · exact Channel.lc_le_any hle hChan
    · exact ih hle hProc
    · exact hlc

  case link =>
    simp [Proc.lc]
    intro hx hy
    constructor
    · exact Channel.lc_le_any hle hx
    · exact Channel.lc_le_any hle hy

lemma Channel.lc_le {u : Channel} {k : Nat} :
  u.lc k → u.lc (k + 1) := by
  intro h
  exact (Channel.lc_le_any) (by simp) h

lemma Proc.lc_le {P : Proc} {k n : Nat} :
  P.lc k n → P.lc (k + 1) n := by
  intro h
  exact (Proc.lc_le_any) (by simp) h

@[simp] lemma Channel.lc_bound {k i : Nat} (hl : i < k) :
  Channel.lc k (.bound i) := by simp [Channel.lc, hl]

@[simp] lemma Channel.lc_close {u : Channel} {x : FPName} {k i : Nat} (hle : i ≤ k) :
  u.lc k → u⟪i | x⟫.lc (k + 1) := by
  induction u
  case free y =>
    intro h
    simp [Channel.lc, HasClose.close_, Channel.close]
    split_ifs
    case pos heq => subst heq ; grind
    case neg hneq => simp
  case bound i =>
    simp [Channel.lc, HasClose.close_, Channel.close]
    grind

@[simp] lemma Proc.lc_close {P : Proc} {x : FPName} {n k i : Nat} (hle : i ≤ k) :
  P.lc k n → P⟪i | x⟫.lc (k + 1) n := by
  induction P generalizing n k i

  case nil =>
    simp [Proc.lc]

  case one ih | bot ih | selectL ih | selectR ih | input ih | server ih | consume ih
    | dispose ih =>
    simp [Proc.lc]
    intro hChan hProc
    constructor
    · exact Channel.lc_close hle hChan
    · apply ih hle hProc

  case tensor ih | parr ih | duplicate ih =>
    simp [Proc.lc]
    intro hChan hProc
    constructor
    · exact Channel.lc_close hle hChan
    · apply ih (by simp [hle]) hProc

  case cut ih =>
    simp [Proc.lc] at ⊢ ih
    apply ih
    grind

  case par ihP ihQ =>
    simp [Proc.lc] at ⊢ ihP ihQ
    intro hP hQ
    constructor
    · exact ihP hle hP
    · exact ihQ hle hQ

  case amp ihP ihQ =>
    simp [Proc.lc] at ⊢ ihP ihQ
    intro hChan hP hQ
    split_ands
    · exact Channel.lc_close hle hChan
    · exact ihP hle hP
    · exact ihQ hle hQ

  case output ih =>
    simp [Proc.lc] at ⊢ ih
    intro hChan hProc hType
    split_ands
    · exact Channel.lc_close hle hChan
    · exact ih hle hProc
    · exact hType

  case link =>
    simp [Proc.lc]
    intro hx hy
    constructor
    · exact Channel.lc_close hle hx
    · exact Channel.lc_close hle hy

lemma Channel.close_substNames_comm_gen {u : Channel} {x y z : FPName} {k : Nat}
  (hzx : z ≠ x) (hzy : z ≠ y) :
  u⟪k | z⟫{y // x} = u{y // x}⟪k | z⟫ := by
  induction u
  case free =>
    simp [HasClose.close_, Channel.close, HasSubst.subst, Channel.subst]
    split_ifs
    case pos h1 h2 => subst h1 h2 ; contradiction
    case neg h1 h2 => simp [h1]
    case pos h1 h2 => subst h2 ; simp [hzy]
    case neg h1 h2 => simp ; split_ifs ; rfl

  case bound =>
    simp [HasClose.close_, Channel.close, HasSubst.subst, Channel.subst]

lemma Proc.close_substNames_comm_gen {P : Proc} {x y z : FPName} {k : Nat}
  (hzx : z ≠ x) (hzy : z ≠ y) :
  P⟪k | z⟫{y // x} = P{y // x}⟪k | z⟫ := by
  induction P generalizing k <;> try simp

  case one ih | bot ih | tensor ih | parr ih | selectL ih | selectR ih | output ih | input ih
    | server ih | consume ih | duplicate ih | dispose ih =>
    exact ⟨Channel.close_substNames_comm_gen hzx hzy, ih⟩

  case cut ih => exact ih
  case par ihP ihQ => exact ⟨ihP, ihQ⟩
  case amp ihP ihQ => exact ⟨Channel.close_substNames_comm_gen hzx hzy, ⟨ihP, ihQ⟩⟩
  case link => simp [Channel.close_substNames_comm_gen hzx hzy]

lemma Proc.close_substNames_comm {P : Proc} {x y z : FPName} (hzx : z ≠ x) (hzy : z ≠ y) :
  P⟪z⟫{y // x} = P{y // x}⟪z⟫ := Proc.close_substNames_comm_gen (k := 0) hzx hzy

lemma Proc.closeCut_substNames_comm {P : Proc} {x y z w : FPName}
  (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) :
  P⟪z, w⟫{y // x} = P{y // x}⟪z, w⟫ := by
  simp [HasCloseTwo.close_, HasSubst.subst]
  change P⟪1 | w⟫⟪z⟫{y // x} = P{y // x}⟪1 | w⟫⟪z⟫
  rw [Proc.close_substNames_comm_gen (k := 0) hzx hzy]
  rw [Proc.close_substNames_comm_gen (k := 1) hwx hwy]

lemma Proc.closeAll_open_substNames {P : Proc} {names : List FPName} {y z : FPName} {k n : Nat}
  (hF : z ∉ P.f) (hlc : lc k n P) (hNodup : (names ++ [y]).Nodup) (hFz : z ∉ names) :
  (closeAll P k (names ++ [y]))⸨k + names.length | #z⸩ = closeAll (P{z // y}) k names := by
  induction names generalizing k P
  case nil =>
    simp [closeAll]
    rw [Proc.close_open_eq_substNames]
    · exact hF
    · exact hlc

  case cons fst names ih =>
    simp [← ne_eq, closeAll] at ⊢ hNodup hFz

    have := ih
      (k := k + 1) (P := P⟪k | fst⟫) (by simp [hF])
      (Proc.lc_close (by simp) hlc) hNodup.2 hFz.2
    rw [Nat.add_assoc, Nat.add_comm 1 names.length] at this

    rw [Proc.close_substNames_comm_gen] at this
    · exact this
    · exact hNodup.1.2
    · apply (hFz.1).symm

lemma Proc.open_wrapDup {P : Proc} {names : List FPName} {z : FPName} {k : Nat} :
  (wrapDup P names)⸨k | #z⸩ = wrapDup (P⸨k + names.length | #z⸩) names := by
  induction names generalizing k
  case nil =>
    simp [wrapDup]
  case cons y ys ih =>
    simp only [wrapDup, HasOpen.open_, Proc.open, List.length_cons] at ⊢ ih
    rw [ih]
    congr 2
    grind

lemma Env.not_mem_names_substNames {Γ : Env} {x y z : FPName} (hzy : z ≠ y) (hz : z ∉ Γ.names) :
  z ∉ Γ{y // x}.names := by
  induction Γ
  case nil => simp
  case cons E Δ ih =>
    obtain ⟨w, T⟩ := E
    simp at ⊢ hz
    constructor
    · simp [HasSubst.subst, FPName.subst]
      split_ifs
      case pos => exact hzy
      case neg => exact hz.1
    · simp_all

@[simp] lemma Env.lc_nil {n : Nat} :
  Env.lc n ([] : Env) := by simp [Env.lc]

lemma Env.substNames_preserves_lc {Γ : Env} {x y : FPName} {n : Nat} (hlc : Env.lc n Γ) :
  Env.lc n Γ{y // x} := by
  induction Γ
  case nil => simp
  case cons E Δ ih =>
    obtain ⟨w, T⟩ := E
    simp [Env.lc_cons] at ⊢ hlc
    constructor
    · exact hlc.1
    · apply ih
      exact hlc.2

lemma Env.serverUsable_perm_mp {Γ Δ : Env} :
  Γ ~ Δ → (?ₑΓ → ?ₑΔ) := by
  intro hP hServ A B
  simp [Env.serverUsable] at hServ
  have hAΓ : A ∈ Γ := (hP.mem_iff).mpr B
  exact hServ A.1 A.2 hAΓ

lemma Env.serverUsable_perm_iff {Γ Δ : Env} :
  Γ ~ Δ → (?ₑΓ ↔ ?ₑΔ) := by
  intro hP
  constructor
  · exact Env.serverUsable_perm_mp hP
  · exact Env.serverUsable_perm_mp hP.symm

lemma Env.serverUsable_merge_mp {Γ Δ : Env} :
  ?ₑ(Γ ++ Δ) → (?ₑΓ ∧ ?ₑΔ) := by
  simp [Env.serverUsable]
  intro h
  constructor
  · intro a b hΓ
    exact h a b (Or.inl hΓ)
  · intro a b hΔ
    exact h a b (Or.inr hΔ)

lemma Env.serverUsable_merge_mpr {Γ Δ : Env} :
  (?ₑΓ ∧ ?ₑΔ) → ?ₑ(Γ ++ Δ) := by
  simp [Env.serverUsable]
  intro hΓ hΔ a b h
  cases h
  case inl h => exact hΓ a b h
  case inr h => exact hΔ a b h

lemma Env.serverUsable_merge_iff {Γ Δ : Env} :
  ?ₑ(Γ ++ Δ) ↔ (?ₑΓ ∧ ?ₑΔ) := by
  constructor
  · exact Env.serverUsable_merge_mp
  · exact Env.serverUsable_merge_mpr

lemma Env.Nodup_merge_iff {Γ Δ : Env} :
  (Γ ++ Δ).Nodup ↔ (Γ.Nodup ∧ Δ.Nodup ∧ Γ.disjoint Δ) := by
  simp [Env.Nodup]
  constructor
  · intro h
    have h' := (List.nodup_append.mp h)
    split_ands
    · exact h'.1
    · exact h'.2.1
    · simp [Disjoint]
      intro x hxΓ hxΔ
      ext a
      constructor
      · intro ha
        rcases h' with ⟨_, _, hdis⟩
        have hΓ := hxΓ ha
        have hΔ := hxΔ ha
        have : a ≠ a := hdis a (by simpa using hΓ) a (by simpa using hΔ)
        exact (this rfl).elim
      · intro h; cases h
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    have := (List.nodup_append.mpr ⟨h1, h2, ?_⟩)
    · exact this
    · simp [Disjoint] at h3
      intro a ha b hb hEq
      have hsubsetΓ : ({a} : Finset FPName) ⊆ Γ.names := by
        intro x hx
        simp at hx
        subst hx
        simpa using ha

      have hsubsetΔ : ({a} : Finset FPName) ⊆ Δ.names := by
        intro x hx
        simp at hx
        subst hx
        simpa [hEq] using hb

      have hEmpty := h3 hsubsetΓ hsubsetΔ
      simp at hEmpty

lemma Env.mem_unique {Γ : Env} {x : FPName} {A B : Types}
  (hNodup : Γ.Nodup) (hA : (x, A) ∈ Γ) (hB : (x, B) ∈ Γ) : A = B := by
  induction Γ
  case nil => contradiction
  case cons hd tl ih =>
    obtain ⟨w, T⟩ := hd
    simp_all
    rw [Env.Nodup_cons] at hNodup
    grind [mem_pair_fst_in_names_iff]

lemma Typing_buildDup_aux {n : Nat} {QL QR : Proc} {x : FPName} {A : Types}
  (names : List FPName) (Γ Γ' ΓL : Env) (hTL : n ⊢ QL ∷ [x ∶ A :: ΓL])
  (hTR : n ⊢ QR ∷ [x ∶ A :: Γ]) (h_valid_names : ∀ z ∈ names, z ∈ Γ.names)
  (h_sync_types : ∀ z A, z ∈ names → (z, A) ∈ Γ → (z, A) ∈ ΓL)
  (hNodup : Γ.Nodup) (hD : Γ.disjoint Γ') (hServΓ : ?ₑΓ) (hServΓ' : ?ₑΓ') (hServL : ?ₑΓL)
  (hxΓ : x ∉ Γ.names) (hxΓ' : x ∉ Γ'.names) (hxΓL : x ∉ ΓL.names)
  (hlcΓ : Env.lc n Γ) (hlcΓ' : Env.lc n Γ') (hlcΓL : Env.lc n ΓL)
  (hNodup_names : names.Nodup) (h_part : ∃ Δ, ΓL ~ Δ ++ Γ' ∧ Δ.names = names.toFinset) :

  n ⊢ wrapDup (#x⟦$N⟧․closeAll (!(#x)⟪x⟫․{QL⟪x⟫}) 1 names.reverse |ₚ !#x․{QR}) names ∷
      [x ∶ !!A ⨂ !!A :: Γ ++ Γ'] := by

  induction names generalizing QL Γ' ΓL

  case nil =>
    simp [wrapDup]
    apply Typing.exchange_env (Γ := x ∶ !!A ⨂ !!A :: Γ' ++ Γ)
    · refine Typing.tensor ⟨hxΓ', hxΓ⟩ ({x} ∪ Γ.names ∪ Γ'.names ∪ ΓL.names) ?_
      intro y hy
      simp only [Proc.open_server, Proc.open_par]
      simp [← ne_eq] at hy
      have hQLf:= Typing.f_eq_names hTL
      have hFyQL : y ∉ QL.f := by
        simp [hQLf]
        exact ⟨hy.1, hy.2.2.2⟩
      have hFyQR : y ∉ QR.f := by simp [Typing.f_eq_names hTR, hy]
      have hlcQL := Typing_preserves_lc_proc hTL
      have hlcQR := Typing_preserves_lc_proc hTR

      apply Typing.mix
      · simp_all [← ne_eq]
        constructor
        · exact hy.1.symm
        · exact hD.symm
      · simp [closeAll] at ⊢
        rw [Proc.close_open_eq_substNames hFyQL hlcQL]
        apply Typing.bang (hServΓ')

        have := Typing_substNames (x := x) (y := y) hTL
        simp [Env.substNames_of_not_mem hxΓL] at this
        apply Typing.exchange_env (Γ := y ∶ A :: ΓL)
        · apply this
          intros T h
          cases h with
          | inl h => exact h.1
          | inr h => exfalso ; exact hy.2.2.2 T h
        · obtain ⟨Δ, hPΓL, hNamesΔ⟩ := h_part
          have hNilΔ : Δ = [] := by
            cases Δ
            case nil => rfl
            case cons hd tl => simp [Env.names] at hNamesΔ
          rw [hNilΔ] at hPΓL
          simp only [List.nil_append, HasPerm.perm] at hPΓL
          exact List.Perm.cons (y ∶ A) hPΓL

      · simp
        rw [Proc.open_lc_0]
        · apply Typing.bang hServΓ hTR
        · exact hFyQR
        · exact hlcQR

    · simp [HasPerm.perm]
      apply List.perm_append_comm

  case cons w ws ih =>
    simp [wrapDup] at ⊢

    have hwΓ : w ∈ Γ.names := by apply h_valid_names ; simp

    obtain ⟨B, Δ, hP, hServΔ, hNamesΔ⟩ := Env.extract_exp (Γ := Γ) hwΓ hServΓ hNodup

    have hin : ∃ B Δ, Γ ~ w ∶ ??B :: Δ := by use B, Δ
    have hwx : w ≠ x := by intro hc ; subst hc ; exact hxΓ hwΓ

    apply Typing.exchange_env (Γ := w ∶ ??B :: x ∶ !!A ⨂ !!A :: Δ ++ Γ')
    · refine Typing.c ?_ ({x} ∪ Γ.names ∪ Γ'.names ∪ ΓL.names ∪ ws.reverse.toFinset) ?_
      · simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff]
        split_ands
        · exact hwx
        · grind
        · exact Disjoint.notMem_of_mem_left_finset hD hwΓ
      · intro z hz
        simp [← ne_eq] at hz
        rw [Proc.open_wrapDup]
        simp only [Proc.open_tensor, Channel.open_free_not_eq, Proc.open_par, Proc.open_server]
        have h_close :
          (closeAll (!$0․{QL⟪x⟫}) 1 (ws.reverse ++ [w]))⸨0 + ws.length + 1 | #z⸩ =
            closeAll (!$0․{QL⟪x⟫}){z // w} 1 ws.reverse := by
          have h_idx : 0 + ws.length + 1 = 1 + ws.reverse.length := by
            rw [List.length_reverse]
            omega
          rw [h_idx]
          apply Proc.closeAll_open_substNames
          · have hFzQL : z ∉ QL.f := by
              simp [Typing.f_eq_names hTL]
              exact ⟨hz.1, hz.2.2.2.1⟩
            simp ; intro h ; exfalso ; exact hFzQL h
          · simp [Proc.lc]
            exact Proc.lc_close (by simp) (Typing_preserves_lc_proc hTL)
          · grind
          · simp_all
        rw [h_close]
        simp [Channel.subst_bound]
        have heqQR: QR⸨ws.length + 1 | #z⸩ = QR := by
          rw [Proc.open_lc]
          · simp [Typing.f_eq_names hTR]
            exact ⟨hz.1, hz.2.1⟩
          · exact Proc.lc_le_any (by simp) (Typing_preserves_lc_proc hTR)

        rw [heqQR]
        rw [Proc.close_substNames_comm_gen (hwx.symm) (hz.1.symm)]
        apply Typing.exchange_env (Γ := x ∶ !!A ⨂ !!A :: Γ ++ (z ∶ ??B :: Γ'))
        · simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff] at ih

          obtain ⟨Ξ, hPΓL, hNamesΞ⟩ := h_part
          have hExt : ∃ Ξ', Ξ ~ w ∶ ??B :: Ξ' := by
            have hwΞ: w ∈ Ξ.names := by simp [hNamesΞ]
            have hServΞ :=
              (Env.serverUsable_merge_mp ((Env.serverUsable_perm_iff hPΓL).mp hServL)).1

            have hNodupΓL := (Typing_preserves_linearity hTL).1
            simp [HyperEnv.Nodup] at hNodupΓL
            rw [Env.Nodup_cons] at hNodupΓL
            have hNodupΞ := by
              have := Env.Nodup_perm hPΓL hNodupΓL.2
              simp [Env.Nodup_merge_iff] at this
              exact this.1

            obtain ⟨T, E, hPE, hServE, hNamesE⟩ := Env.extract_exp hwΞ hServΞ hNodupΞ

            have heqBT : T = B := by
              have h_wB_Γ : (w, ??B) ∈ Γ :=
                hP.symm.subset (List.Mem.head _)

              have h_wB_ΓL : (w, ??B) ∈ ΓL := by
                apply h_sync_types w (??B)
                · exact List.Mem.head _
                · exact h_wB_Γ

              have h_wT_Ξ : (w, ??T) ∈ Ξ :=
                hPE.symm.subset (List.Mem.head _)

              have h_wT_ΓL : (w, ??T) ∈ ΓL := by
                have h_app : (w, ??T) ∈ Ξ ++ Γ' := List.mem_append_left Γ' h_wT_Ξ
                exact hPΓL.symm.subset h_app

              have h_eq_types : ??T = ??B := by
                apply Env.mem_unique hNodupΓL.2 h_wT_ΓL h_wB_ΓL

              injection h_eq_types with h_eq

            rw [heqBT] at hPE
            use E

          obtain ⟨Ξ', hPΞ⟩ := hExt

          apply ih (z ∶ ??B :: Γ') (ΓL{z // w}) (x := Ξ')
          · have := Typing_substNames hTL (y := z) (x := w)
            simp [FPName.subst_self_of_ne hwx.symm] at this
            apply this
            intro A h
            cases h with
            | inl h => exfalso ; exact hz.1 h.1
            | inr h => exfalso ; apply hz.2.2.2.1 A h
          · intros a ha
            exact h_valid_names a ((List.mem_cons).mpr (Or.inr ha))
          · intros y T hyws hyΓ
            have := h_sync_types y T ((List.mem_cons).mpr (Or.inr hyws)) hyΓ
            have hnyw : y ≠ w := by
              simp [List.nodup_cons] at hNodup_names
              intro hc
              subst hc
              exact hNodup_names.1 hyws
            exact Env.mem_substNames_of_ne this hnyw
          · simp_all
          · exact Env.serverUsable_cons_iff.mp ⟨by simp [Types.isServerUsable], hServΓ'⟩
          · exact Env.serverUsable_substNames hServL
          · simp [- Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff]
            exact ⟨hz.1.symm, hxΓ'⟩
          · exact Env.not_mem_names_substNames hz.1.symm hxΓL
          · have := (Env.lc_perm hP).mp hlcΓ
            simp [Env.lc_cons] at ⊢ this
            exact ⟨this.1, hlcΓ'⟩
          · exact Env.substNames_preserves_lc hlcΓL
          · simp at hNodup_names
            exact hNodup_names.2
          · have h1: Ξ ++ Γ' ~ w ∶ ??B :: Ξ' ++ Γ' := by
              apply List.Perm.append
              · simp [HasPerm.perm] at hPΞ
                exact hPΞ
              · rfl

            have hnwΓ':= Disjoint.notMem_of_mem_left_finset hD hwΓ

            have hnwΞ := by
              have hndΓL := by
                have := (HyperEnv.Nodup_cons (Typing_preserves_linearity hTL).1).2
                simp [HyperEnv.Nodup] at this
                exact this
              have := Env.Nodup_perm hPΞ (Env.Nodup_merge_iff.mp (Env.Nodup_perm hPΓL hndΓL)).1
              simp only [Env.Nodup_cons] at this
              exact this.1

            have := Env.substNames_preserves_perm (x := w) (y := z)
              (List.Perm.trans (List.Perm.trans hPΓL h1) List.perm_middle.symm)
            simp at this hNodup_names

            rw [Env.substNames_of_not_mem hnwΓ', Env.substNames_of_not_mem hnwΞ] at this

            exact this

          · have hnwΞ := by
              have hndΓL := by
                have := (HyperEnv.Nodup_cons (Typing_preserves_linearity hTL).1).2
                simp [HyperEnv.Nodup] at this
                exact this
              have := Env.Nodup_perm hPΞ (Env.Nodup_merge_iff.mp (Env.Nodup_perm hPΓL hndΓL)).1
              simp only [Env.Nodup_cons] at this
              exact this.1

            simp at hNodup_names
            have := Env.names_eq_of_perm hPΞ
            rw [hNamesΞ] at this
            simp at this
            have hnwws: w ∉ ws.toFinset := by simp [hNodup_names.1]

            have h : (insert w ws.toFinset).erase w = (insert w (Env.names Ξ')).erase w := by
              rw [this]

            rw [Finset.erase_insert hnwws, Finset.erase_insert hnwΞ] at h
            exact h.symm

        · simp [HasPerm.perm] at ⊢ hP
          apply List.Perm.trans
          · apply List.Perm.cons
            apply List.Perm.append_right
            exact hP
          · apply List.Perm.trans
            · apply List.Perm.swap
            · apply List.Perm.cons
              apply List.Perm.trans
              · apply List.Perm.cons
                apply List.perm_middle
              · apply List.Perm.swap

    · simp [HasPerm.perm] at ⊢ hP
      apply List.Perm.trans
      · apply List.Perm.swap
      · apply List.Perm.cons
        apply List.Perm.append_right _ hP.symm

lemma Typing_buildDup {n : Nat} {P : Proc} {x : FPName} {A : Types} {Γ : Env}
  {names : List FPName} (hServ : ?ₑΓ) (heq_names : names.toFinset = Γ.names)
  (hnd_names : names.Nodup) (hT : n ⊢ P ∷ [x ∶ A :: Γ]) :
  n ⊢ buildDup P names x ∷ [x ∶ !!A ⨂ !!A :: Γ] := by
  rw [← Env.merge_unitR Γ]
  change n ⊢ wrapDup (#x⟦$N⟧․closeAll (!(#x)⟪x⟫․{P⟪x⟫}) 1 names.reverse |ₚ !#x․{P}) names ∷
    [x ∶ !!A ⨂ !!A :: Γ ++ []]

  have hlin := Typing_preserves_linearity hT
  have hndΓ := (HyperEnv.Nodup_cons hlin.1).2
  have hlcT := Typing_preserves_lc hT
  have hlcΓx := hlcT.2 (x ∶ A :: Γ)
  simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff,
    HyperEnv.Nodup, Env.Nodup_cons, Env.lc_cons] at hndΓ hlin hlcΓx

  apply Typing_buildDup_aux names Γ [] Γ
  · exact hT
  · exact hT
  · intro z hz
    have hznames : z ∈ names.toFinset := by simp [hz]
    rw [heq_names] at hznames
    exact hznames
  · intros z A hznames hzΓ ; exact hzΓ
  · exact hndΓ
  · simp
  · exact hServ
  · simp
  · exact hServ
  · have := (Typing_preserves_linearity hT).1
    apply HyperEnv.Nodup_singleton at this
    rw [Env.Nodup_cons] at this
    exact this.1
  · simp
  · exact hlin.1
  · exact hlcΓx.2
  · simp
  · exact hlcΓx.2
  · exact hnd_names
  · use Γ ; simp [HasPerm.perm, heq_names]




lemma Typing_inv_res {n : ℕ} {P : Proc} {𝒢 : HyperEnv}
  (hT : n ⊢ 𝑣⸨$N,$N⸩ P ∷ 𝒢) :
  ∃ (A : Types) (Γ Δ : Env) (𝒢' : HyperEnv) (L : Finset FPName),
    (𝒢 ~ 𝒢' |ₕ [Γ‚ Δ]) ∧
    (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      n ⊢ P⸨#x, #y⸩ ∷ 𝒢' |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) := by

  generalize heq : (𝑣⸨$N,$N⸩ P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨A, Γ, Δ, 𝒢, L, hP', hT'⟩ := ih heq
    use A, Γ, Δ, 𝒢, L
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.cons hP.symm (by rfl)) hP'
    · intros x hx y hy hneq
      exact hT' x hx y hy hneq

  case exchange_hyper hP ih =>
    obtain ⟨A, Γ, Δ, 𝒢, L, hP', hT'⟩ := ih heq
    use A, Γ, Δ, 𝒢, L
    constructor
    · exact HyperEnv.Perm.trans hP.symm hP'
    · intros x hx y hy hneq
      exact hT' x hx y hy hneq

  case cut 𝒢 Γ Δ _ A _ L hT ih =>
    use A, Γ, Δ, 𝒢, L
    constructor
    · rfl
    · injection heq with heq
      subst heq
      intros x hx y hy hneq
      exact hT x y hx hy hneq




lemma HyperEnv.merge_nilL (𝒢 : HyperEnv) : [] |ₕ 𝒢 = 𝒢 := by simp

lemma HyperEnv.merge_nilR (𝒢 : HyperEnv) : 𝒢 |ₕ [] = 𝒢 := by simp

lemma HyperEnv.Perm.merge_right {𝒢 ℋ : HyperEnv} (p : 𝒢 ~ ℋ) : ∀ 𝒥, 𝒢 |ₕ 𝒥 ~ ℋ |ₕ 𝒥 := by
  induction p
  case nil => simp
  case cons hPE hPH ih => intro 𝒥 ; exact HyperEnv.Perm.cons hPE (ih 𝒥)
  case swap => intro 𝒥 ; exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => intro 𝒥 ; exact HyperEnv.Perm.trans (ih1 𝒥) (ih2 𝒥)

theorem HyperEnv.Perm.merge_left {𝒢 ℋ : HyperEnv} : 𝒢 ~ ℋ → ∀ 𝒥, 𝒥 |ₕ 𝒢 ~ 𝒥 |ₕ ℋ := by
  intro h 𝒥
  induction 𝒥
  case nil => exact h
  case cons Γ ℐ ih => apply HyperEnv.Perm.cons (.refl _) ih

theorem HyperEnv.Perm.merge {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
  𝒢 |ₕ ℋ ~ 𝒢' |ₕ ℋ' := (p₁.merge_right ℋ).trans (p₂.merge_left _)

@[simp] lemma HyperEnv.Perm_middle {Γ : Env} : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ Γ :: ℋ ~ Γ :: (𝒢 |ₕ ℋ)
  | [], _ => .refl _
  | Δ :: _, _ =>
    (HyperEnv.Perm.cons (.refl _) Perm_middle).trans (HyperEnv.Perm.swap Δ Γ _)

lemma HyperEnv.Perm.merge_exchange_right {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (𝒢 |ₕ ℋ ~ 𝒢 |ₕ 𝒥) := by
  intro h
  induction 𝒢
  case nil => simp ; exact h
  case cons ih => apply HyperEnv.Perm.cons (by rfl) ih

lemma HyperEnv.Perm.merge_exchange_left {𝒢 ℋ 𝒥 : HyperEnv} :
  ℋ ~ 𝒥 → (ℋ |ₕ 𝒢 ~ 𝒥 |ₕ 𝒢 ) := by
  intro h
  induction h
  case nil => simp
  case cons hPE hPH ih => exact HyperEnv.Perm.cons hPE ih
  case swap => exact HyperEnv.Perm.swap ..
  case trans ih1 ih2 => exact HyperEnv.Perm.trans ih1 ih2

lemma HyperEnv.Perm.merge_comm : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ ℋ ~ ℋ |ₕ 𝒢
  | [], _ => by simp
  | _ :: _, _ => (HyperEnv.Perm.merge_comm.cons (.refl _)).trans HyperEnv.Perm_middle.symm

lemma HyperEnv.merge_assoc (𝒢 ℋ ℐ : HyperEnv) : 𝒢 |ₕ ℋ |ₕ ℐ = 𝒢 |ₕ (ℋ |ₕ ℐ) := by
  simp only [List.append_assoc]

lemma HyperEnv.Perm.merge_assoc (𝒢 ℋ ℐ : HyperEnv) :
  (𝒢 |ₕ (ℋ |ₕ ℐ)) ~ (ℋ |ₕ (𝒢 |ₕ ℐ)) := by
  repeat rw [← HyperEnv.merge_assoc]
  apply HyperEnv.Perm.merge_right HyperEnv.Perm.merge_comm

lemma HyperEnv.Perm.merge_cons {Γ : Env} {𝒢 𝒢' ℋ ℋ' : HyperEnv} (p₁ : 𝒢 ~ 𝒢') (p₂ : ℋ ~ ℋ') :
    𝒢 |ₕ Γ :: ℋ ~ 𝒢' |ₕ Γ :: ℋ' := p₁.merge (p₂.cons (.refl _))

@[simp] lemma HyperEnv.Perm_merge_singleton (Γ : Env) (𝒢 : HyperEnv) : 𝒢 |ₕ [Γ] ~ Γ :: 𝒢 :=
  HyperEnv.Perm_middle.trans <| by rw [HyperEnv.merge_nilR]

lemma HyperEnv.Perm_merge_comm : ∀ {𝒢 ℋ : HyperEnv}, 𝒢 |ₕ ℋ ~ ℋ |ₕ 𝒢
  | [], _ => by simp
  | _ :: _, _ => (HyperEnv.Perm_merge_comm.cons (.refl _)).trans HyperEnv.Perm_middle.symm

theorem HyperEnv.Perm_merge_comm_assoc (𝒢 ℋ 𝒥 : HyperEnv) :
    (𝒢 |ₕ (ℋ |ₕ 𝒥)) ~ (ℋ |ₕ (𝒢 |ₕ 𝒥)) := by
  simpa only [List.append_assoc] using HyperEnv.Perm_merge_comm.merge_right _

lemma HyperEnv.cons_rotate_left (𝒢 : HyperEnv) (Γ : Env) :
  (Γ :: 𝒢) ~ (𝒢 |ₕ [Γ]) := by
  symm ; apply HyperEnv.Perm_merge_singleton





-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr
-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere






-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs
-- FIXME: Find different syntax for open?
-- FIXME: Prove name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }

-- TODO: Implement the following instead of having post condition on res in EnvStep
-- NOTE: Not possible without knowning that l.i is disjoint form ℋ, which could be
-- obtained from a ProcStep sidecondition, but that would require having this be used
-- inside e.g. session_fidelity and not having it be a strictly stand alone property /
-- lemma for EnvStep - This would also need to know the corresponding ProcStep and Typing.
-- But could work as an auxiliary for session fidelity, not standalone for EnvStep.
-- lemma EnvStep.Linearity_and_subset {𝒢 𝒢' : HyperEnv} {l : Lbl}
--   (hlin : 𝒢.Linearity) (hES : 𝒢 -[l]->ₑ 𝒢') :
--   𝒢'.Linearity ∧ (𝒢'.names ⊆ 𝒢.names ∪ l.i) := by
--   induction hES




-- FIXME: Currently HyperEnv.Nodup is only internal for each parallel componenet
--        and PairwiseDisjoint checks intra disjointess for components.
--        Change this to have global no duplicates predicate using current Nodup
--        and PairwiseDisjoint.


lemma HyperEnv.disjoint_names_left {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint 𝒢.names S ↔ ∀ Γ ∈ 𝒢, Disjoint Γ.names S := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

lemma HyperEnv.disjoint_names_right {𝒢 : HyperEnv} {S : Finset FPName} :
  Disjoint S 𝒢.names ↔ ∀ Γ ∈ 𝒢, Disjoint S Γ.names := by
  induction 𝒢
  case nil => simp
  case cons ih =>
    simp [HyperEnv.names_cons]
    intro
    apply ih

def HyperEnv.Linearity (𝒢 : HyperEnv) : Prop :=
  𝒢.Nodup ∧ 𝒢.PairwiseDisjoint

lemma HyperEnv.Perm_preserves_Linearity {𝒢 ℋ : HyperEnv} :
  𝒢 ~ ℋ → (𝒢.Linearity ↔ ℋ.Linearity) := by
  intro h
  simp [HyperEnv.Linearity, HyperEnv.PairwiseDisjoint]
  rw [HyperEnv.Nodup_perm_iff h, HyperEnv.Perm_PairwiseDisjoint_iff h]

lemma HyperEnv.Perm.preserves_Linearity {𝒢 ℋ : HyperEnv}
  (hP : 𝒢 ~ ℋ) (h : 𝒢.Linearity) : ℋ.Linearity :=
  (HyperEnv.Perm_preserves_Linearity hP).mp h

@[simp] lemma HyperEnv.Linearity_nil :
  HyperEnv.Linearity [] := by simp [HyperEnv.Linearity]

@[simp] lemma HyperEnv.Linearity_singleton {Γ : Env} :
  HyperEnv.Linearity [Γ] = Γ.Nodup := by
  simp [HyperEnv.Linearity, HyperEnv.Nodup]

@[simp] lemma HyperEnv.Linearity_merge {𝒢 ℋ : HyperEnv} :
  (𝒢 |ₕ ℋ).Linearity = (𝒢.Linearity ∧ ℋ.Linearity ∧
    ∀ a ∈ 𝒢, ∀ b ∈ ℋ, Disjoint a.names b.names) := by
  simp [HyperEnv.Linearity]
  constructor
  · intro h
    obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
    exact ⟨⟨h1, h3⟩, ⟨⟨h2, h4⟩, h5⟩⟩
  · intro h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
    exact ⟨⟨h1, h3⟩, h2, h4, h5⟩

-- NOTE: There have been placed additional constraints on par₁, par₂, res and syn in EnvStep to
-- make this a standalone property, and getting it to type check. Ideally, these would be removed
-- and mutual induction would be done on ProcStep and EnvStep related by a valid Typing instead.
-- The added contraints are either provided by constraints on ProcStep or can be extracted from
-- The Typing relation using the `Typing_preserves_XXX` lemmas.
lemma EnvStep.preserves_Linearity {𝒢 𝒢' : HyperEnv} {l : Lbl}
  (hlin : 𝒢.Linearity) (hES : 𝒢 -[l]->ₑ 𝒢') : 𝒢'.Linearity := by
  induction hES

  case one | link₁ => simp

  case tensor hF =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons, Env.Nodup_merge_iff] at ⊢ hlin hF
    split_ands
    · exact hF.2.1
    · exact hlin.2.1
    · exact hlin.1.2
    · exact hlin.2.2.1
    · simp_all [← ne_eq, HyperEnv.PairwiseDisjoint]
      exact hF.1.symm

  case bot =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hlin
    exact hlin.2

  case parr hF =>
    simp [HyperEnv.Linearity, HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hlin hF
    constructor
    · exact hF
    · exact hlin

  case par₁ hES hDl ih =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin
    constructor
    · exact ih hlin𝒢
    · constructor
      · exact hlinℋ
      · intro E1 hE1 E2 hE2
        have hsub𝒢'𝒢:= EnvStep.names_subset hES
        have hsubE1 :=
          Finset.Subset.trans (HyperEnv.subset_names_of_mem hE1) hsub𝒢'𝒢
        apply Finset.disjoint_of_subset_left hsubE1
        rw [Finset.disjoint_union_left]
        constructor
        · rw [HyperEnv.disjoint_names_left]
          intro a ha
          exact hD a ha E2 hE2
        · rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
          exact Finset.disjoint_of_subset_right (HyperEnv.subset_names_of_mem hE2) hDl

  case par₂ hES hDl ih =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin
    constructor
    · exact hlin𝒢
    · constructor
      · exact ih hlinℋ
      · intro E1 hE1 E2 hE2
        have hsubℋ'ℋ := EnvStep.names_subset hES
        have hsubE2 :=
          Finset.Subset.trans (HyperEnv.subset_names_of_mem hE2) hsubℋ'ℋ
        apply Finset.disjoint_of_subset_right hsubE2
        rw [Finset.disjoint_union_right]
        constructor
        · rw [HyperEnv.disjoint_names_right]
          intro a ha
          exact hD E1 hE1 a ha
        · rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
          exact Finset.disjoint_of_subset_left (HyperEnv.subset_names_of_mem hE1) hDl.symm

  case syn hES𝒢 hESℋ hDl lwf ihP ihQ =>
    simp at ⊢ hlin
    obtain ⟨hlin𝒢, hlinℋ, hD⟩ := hlin

    constructor
    · exact ihP hlin𝒢
    · constructor
      · exact ihQ hlinℋ
      · intro E1 hE1 E2 hE2
        rw [← Finset.disjoint_iff_inter_eq_empty] at hDl
        rw [Lbl.WF, ← Finset.disjoint_iff_inter_eq_empty] at lwf
        simp only [HyperEnv.merge, HyperEnv.names_merge, Lbl.i,
          Finset.disjoint_union_left, Finset.disjoint_union_right] at hDl
        obtain ⟨⟨hDl1, hDl2⟩, ⟨hDl3, hDl4⟩⟩ := hDl

        have hsubE1 := Finset.Subset.trans
          (HyperEnv.subset_names_of_mem hE1)
          (EnvStep.names_subset hES𝒢)

        have hsubE2:= Finset.Subset.trans
          (HyperEnv.subset_names_of_mem hE2)
          (EnvStep.names_subset hESℋ)

        apply Finset.disjoint_of_subset_left hsubE1
        apply Finset.disjoint_of_subset_right hsubE2

        rw [Finset.disjoint_union_left, Lbl.i, Lbl.i]
        constructor
        · rw [Finset.disjoint_union_right]
          constructor
          · rw [HyperEnv.disjoint_names_left]
            intro E3 hE3
            rw [HyperEnv.disjoint_names_right]
            intro E4 hE4
            exact hD E3 hE3 E4 hE4
          · exact hDl2.symm
        · rw [Finset.disjoint_union_right]
          constructor
          · exact hDl3
          · exact lwf

  case one_bot | tensor_parr => exact hlin

  case res 𝒢 𝒢' Γ Γ' Δ Δ' x y A B l hFx hFy hFx' hFy' _ _ hneq hES𝒢 ih =>
    simp [Env.Nodup_merge_iff] at hlin ⊢ hFx hFx' hFy hFy'
    obtain ⟨hlin𝒢, ⟨hndΓ, ⟨hndΔ, hDΓΔ⟩⟩, hD⟩ := hlin
    have hlin_inner : (𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]).Linearity := by
      simp
      constructor
      · exact hlin𝒢
      · constructor
        · change HyperEnv.Linearity ([x ∶ Aᗮ :: Γ] |ₕ  [y ∶ A :: Δ])
          simp only [HyperEnv.Linearity_merge]
          constructor
          · simp [Env.Nodup_cons]
            constructor
            · exact hFx.2.1
            · exact hndΓ
          · constructor
            · simp [Env.Nodup_cons]
              constructor
              · exact hFy.2.2
              · exact hndΔ
            · intro a ha b hb
              simp at ha hb
              simp [ha, hb]
              exact ⟨⟨hneq.symm, hFy.2.1⟩, ⟨hFx.2.2, hDΓΔ⟩⟩
        · intro a ha
          obtain ⟨hDΓ, hDΔ⟩ := hD a ha
          refine ⟨⟨?_, hDΓ⟩, ⟨?_, hDΔ⟩⟩
          · intro T hxT
            apply hFx.1
            rw [HyperEnv.mem_pair_fst_in_names]
            use T, a
          · intro T hyT
            apply hFy.1
            rw [HyperEnv.mem_pair_fst_in_names]
            use T, a

    have hlin_outer:= ih hlin_inner

    simp at hlin_outer
    obtain ⟨hlin𝒢', hlin_xy, hD'⟩ := hlin_outer
    change HyperEnv.Linearity ([x ∶ Aᗮ :: Γ'] |ₕ  [y ∶ A :: Δ']) at hlin_xy
    simp only [HyperEnv.Linearity_merge, HyperEnv.Linearity_singleton, Env.Nodup_cons] at hlin_xy
    obtain ⟨hlin_xΓ', hlin_yΔ', hD_xΓ'yΔ'⟩ := hlin_xy
    simp at hD_xΓ'yΔ'

    split_ands
    · exact hlin𝒢'.1
    · exact hlin𝒢'.2
    · exact hlin_xΓ'.2
    · exact hlin_yΔ'.2
    · exact hD_xΓ'yΔ'.2.2
    · intro a ha
      have ⟨⟨_, haΓ'⟩, _, haΔ'⟩:= hD' a ha
      constructor
      · exact haΓ'
      · exact haΔ'

  case selectL | selectR | ampL | ampR | use₁ | use₂ | disp₁ | disp₂
    | dup₁ | dup₂ | output | input =>
    simp [Env.Nodup_cons] at hlin ⊢
    exact hlin

  case perm hP _ hP' ih =>
    exact hP'.preserves_Linearity (ih (hP.symm.preserves_Linearity hlin))
















lemma HyperEnv.Perm.extract_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (h_zx : z ≠ x) (h_zy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hFx' : x ∉ ℋ.names) (hFy' : y ∉ ℋ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by

  have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · rcases h with hE𝒢 | hEΓx
    ·
      obtain ⟨𝒢_rest, hG_split⟩ : ∃ 𝒢_rest, 𝒢 ~ E :: 𝒢_rest := by sorry
      have hG_upgraded : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢_rest := by
        apply HyperEnv.Perm.trans hG_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)

      refine ⟨𝒢_rest |ₕ [Γ‚ Δ], Ξ, ?_, ?_⟩
      · sorry
      · sorry
    · sorry











  obtain ⟨𝒢_rest, hG_split⟩ : ∃ 𝒢_rest, 𝒢 ~ 𝒢_rest |ₕ [z ∶ ⊥ :: Ξ] := by sorry
  refine ⟨𝒢_rest |ₕ [Γ‚ Δ], Ξ, ?_⟩
  constructor
  · sorry
  · sorry



lemma EnvStep_inv_bot {𝒢 𝒢' : HyperEnv} {y : FPName}
  (hnd : 𝒢.Nodup) (hES : 𝒢 -[y⸨⸩]->ₑ 𝒢') :
  ∃ 𝒢ᵣ Γ, (𝒢 ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Γ]) ∧ (𝒢' ~ 𝒢ᵣ |ₕ [Γ]) := by
  generalize hl : (y⸨⸩ : Lbl) = l at hES
  induction hES <;> try contradiction
  all_goals simp at hl

  case bot Γ _ =>
    subst hl
    use ∅, Γ
    simp

  case par₁ ℋ ℋ' 𝒥 l hES _ ih =>
    simp at hnd
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hnd.1 hl
    use (𝒢ᵣ_ih |ₕ 𝒥), Γ_ih
    constructor
    · have h1 := HyperEnv.Perm.merge_right h_pre_ih 𝒥
      have h2 : 𝒢ᵣ_ih |ₕ [y ∶ ⊥ :: Γ_ih] |ₕ 𝒥 ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [y ∶ ⊥ :: Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.merge_comm
      exact HyperEnv.Perm.trans h1 h2
    · have h1 := HyperEnv.Perm.merge_right h_post_ih 𝒥
      have h2 : 𝒢ᵣ_ih |ₕ [Γ_ih] |ₕ 𝒥 ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_left
        apply HyperEnv.Perm.merge_comm
      exact h1.trans h2

  case par₂ 𝒥 ℋ ℋ' l hES _ ih =>
    simp at hnd
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hnd.2 hl
    use (𝒢ᵣ_ih |ₕ 𝒥), Γ_ih
    constructor
    · have h1 := HyperEnv.Perm.merge_left h_pre_ih 𝒥
      have h2 : 𝒥 |ₕ (𝒢ᵣ_ih |ₕ [y ∶ ⊥ :: Γ_ih]) ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [y ∶ ⊥ :: Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_assoc
      exact h1.trans h2
    · have h1 := HyperEnv.Perm.merge_left h_post_ih 𝒥
      have h2 : 𝒥 |ₕ (𝒢ᵣ_ih |ₕ [Γ_ih]) ~ 𝒢ᵣ_ih |ₕ 𝒥 |ₕ [Γ_ih] := by
        repeat rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm.merge_assoc
      exact h1.trans h2

  case res 𝒢 ℋ Γ Γ' Δ Δ' u v A B l hFu hFv hFu' hFv' hFlu hFlv hneq hES ih =>
    simp at hnd
    have := HyperEnv.Nodup_singleton hnd.2
    simp [Env.Nodup_merge_iff] at this
    simp at hFu hFv

    have hndΓu: HyperEnv.Nodup [u ∶ Aᗮ :: Γ] := by
      apply HyperEnv.Nodup_singleton_from_env
      simp [Env.Nodup_cons]
      exact ⟨hFu.2.1, this.1⟩

    have hndΔv : HyperEnv.Nodup [v ∶ A :: Δ] := by
      apply HyperEnv.Nodup_singleton_from_env
      simp [Env.Nodup_cons]
      exact ⟨hFv.2.2, this.2.1⟩

    have hnd' := And.intro (And.intro hnd.1 hndΓu) hndΔv

    simp only [HyperEnv.Nodup_merge] at ih
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hnd' hl

    rw [← hl] at hFlu hFlv
    simp [← ne_eq] at hFlu hFlv
    symm at hFlu hFlv


    sorry
    -- exact HyperEnv.Perm.extract_bot_res h_pre_ih h_post_ih hFlu hFlv

  case perm 𝒢 𝒢' ℋ ℋ' _ hP _ hP' ih =>
    have := HyperEnv.Nodup_perm hP.symm hnd
    obtain ⟨𝒥, Γ, h_pre_ih, h_post_ih⟩ := ih this hl
    use 𝒥, Γ
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP) h_pre_ih
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP') h_post_ih





-- lemma EnvStep_inv_one {𝒢 𝒢' : HyperEnv} {x : FPName}
--   (hES : 𝒢 -[x⟦⟧]->ₑ 𝒢') :
--   ∃ 𝒢_rest, (𝒢 ~ 𝒢_rest |ₕ [[x ∶ 1]]) ∧ (𝒢' ~ 𝒢_rest) := by
--   generalize h_lbl : (x⟦⟧ : Lbl) = lbl at hES
--   induction hES <;> try contradiction
--   all_goals sorry


-- lemma EnvStep_inv_one_bot {𝒢 ℋ : HyperEnv} {x y : FPName}
--   (hES : 𝒢 -[x⟦⟧ |ₗ y⸨⸩]->ₑ ℋ) :
--   ∃ 𝒢' Γ,
--     (𝒢 ~ 𝒢' |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) ∧
--     (ℋ ~ 𝒢 |ₕ [Γ]) := by sorry

  -- generalize h_lbl : (x⟦⟧ |ₗ y⸨⸩) = lbl at hES
  -- induction hES <;> try contradiction









-- FIXME: Check that this covers all rules mentioned in the paper
-- FIXME: Subject reduction / simulation proof
theorem session_fidelity {n : Nat} {P P' : Proc} {𝒢 : HyperEnv} {l : Lbl} :
  Typing n P 𝒢 → ProcStep P l P' →
  ∃ 𝒢', EnvStep 𝒢 l 𝒢' ∧ Typing n P' 𝒢' := by
  intros hT hPS
  induction hPS generalizing n 𝒢

  case one =>
    obtain ⟨hP, 𝒟⟩ := Typing_inv_one hT
    use ∅
    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.one
      · exact HyperEnv.Perm.nil
    · exact 𝒟

  case bot =>
    obtain ⟨Γ, hP, 𝒟⟩ := Typing_inv_bot hT
    use [Γ]
    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.bot
      · apply HyperEnv.Perm.refl
    · exact 𝒟

  case tensor Q x y hF =>
    obtain ⟨A, B, Γ, Δ, L, hP, 𝒟⟩ := Typing_inv_tensor hT
    use ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])

    have := Typing.f_eq_names hT
    simp_rw [HyperEnv.names_eq_of_perm hP] at this
    simp [Channel.f] at this hF
    have h : HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ] = insert x (Γ.names ∪ Δ.names) := by simp

    have hFy : y ∉ HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ] := by
      simp [h, ← this, hF]
    simp at hFy
    obtain ⟨hFy1, hFy2, hFy3⟩ := hFy

    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.tensor (by simp [hFy1, hFy2, hFy3])
      · simp [HasPerm.perm]
    · obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {x, y} ∪ Γ.names ∪ Δ.names ∪ Q.f)
      simp at hz
      obtain ⟨hnzx, hnzy, hz1, hz2, hz3, hz4⟩ := hz
      have 𝒟' := Typing_substNames (x := z) (y := y) (𝒟 z hz1) (by
        intros Γ hΓ T hinΓ
        simp at hΓ
        rcases hΓ with rfl | rfl
        case inl =>
          simp at hinΓ
          rcases hinΓ with ⟨rfl, rfl⟩ | h1
          case inl => rfl
          case inr =>
            have := hFy2 T
            contradiction
        case inr =>
          simp at hinΓ
          rcases hinΓ with ⟨rfl, rfl⟩ | h00
          case inl => contradiction
          case inr =>
            have := hFy3 T
            contradiction
        )
      simp [← Proc.open_substNames_intro (z := y) hz4] at 𝒟'

      rw [FPName.subst_self_of_ne, Env.substNames_of_not_mem, Env.substNames_of_not_mem] at 𝒟'
      · exact 𝒟'
      · rw [Env.mem_pair_fst_in_names_iff]
        intro ⟨T, hT⟩
        exact hz3 T hT
      · rw [Env.mem_pair_fst_in_names_iff]
        intro ⟨T, hT⟩
        exact hz2 T hT
      · intro heq
        exact hnzx heq.symm

  case parr Q x y hF =>
    obtain ⟨A, B, Γ, L, hP, 𝒟⟩ := Typing_inv_parr hT
    use [y ∶ A :: x ∶ B :: Γ]

    have := Typing.f_eq_names hT
    simp_rw [HyperEnv.names_eq_of_perm hP] at this
    simp [Channel.f] at this hF
    have h : HyperEnv.names [x ∶ A ⅋ B :: Γ] = insert x (Γ.names) := by simp

    have hFy : y ∉ HyperEnv.names [x ∶ A ⅋ B :: Γ] := by
      simp [h, ← this, hF]
    simp at hFy
    obtain ⟨hneq, hFy⟩ := hFy

    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.parr (by simp [hneq, hFy])
      · simp [HasPerm.perm]
    · obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {x, y} ∪ Γ.names ∪ Q.f)
      simp at hz
      obtain ⟨hnzx, hnzy, hz1, hz2, hz3⟩ := hz
      have 𝒟' := Typing_substNames (x := z) (y := y) (𝒟 z hz1) (by
        intros Γ hΓ T hinΓ
        simp at hΓ
        subst hΓ
        rcases hinΓ
        case head => contradiction
        case tail hMem =>
          cases hMem
          case head => contradiction
          case tail hMem =>
            cases hMem
            case head Γ =>
              exfalso
              apply hFy T
              exact List.mem_cons_self
            case tail e Γ hMem =>
              exfalso
              apply hFy T
              apply List.mem_cons_of_mem
              exact hMem
        )

      rw [← Proc.open_substNames_intro] at 𝒟'
      · simp at 𝒟'
        rw [FPName.subst_self_of_ne, Env.substNames_of_not_mem] at 𝒟'
        · exact 𝒟'
        · rw [Env.mem_pair_fst_in_names_iff]
          intro ⟨T, hT⟩
          exact hz2 T hT
        · rw [← ne_eq] at hnzx
          exact hnzx.symm
      · exact hz3

  case par₁ hFl ih =>
    obtain ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
    obtain ⟨ℋ₁', hStep, hTP'⟩:= ih hTP
    use ℋ₁' |ₕ ℋ₂
    constructor
    · apply EnvStep.perm hP.symm
      · apply EnvStep.par₁ hStep
        rw [Typing.f_eq_names hTQ] at hFl
        exact hFl
      · apply HyperEnv.Perm.refl
    · apply Typing.mix ?_ hTP' hTQ
      rw [← Finset.disjoint_iff_inter_eq_empty, (Typing.f_eq_names hTQ)] at hFl
      have hD := Typing_preserves_disjointness (Typing.exchange_hyper hT hP)
      exact EnvStep.preserves_disjoint hStep (HyperEnv.disjoint_split hD) hFl

  case par₂ hFl ih =>
    obtain ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
    obtain ⟨ℋ₂', hStep, hTQ'⟩:= ih hTQ
    use ℋ₁ |ₕ ℋ₂'
    constructor
    · apply EnvStep.perm hP.symm
      · apply EnvStep.par₂ hStep
        rw [Typing.f_eq_names hTP] at hFl
        exact hFl
      · apply HyperEnv.Perm_refl
    · apply Typing.mix ?_ hTP hTQ'
      rw [← Finset.disjoint_iff_inter_eq_empty, (Typing.f_eq_names hTP)] at hFl
      have hD := Typing_preserves_disjointness (Typing.exchange_hyper hT hP)
      exact (EnvStep.preserves_disjoint hStep (HyperEnv.disjoint_split hD).symm hFl).symm

  case syn l l' _ _ hFl lwf ihP ihQ =>
    have ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
    have ⟨ℋ₁', hStepP, hTP'⟩ := ihP hTP
    have ⟨ℋ₂', hStepQ, hTQ'⟩ := ihQ hTQ
    use ℋ₁' |ₕ ℋ₂'
    constructor
    · apply EnvStep.perm hP.symm
      · apply EnvStep.syn hStepP hStepQ
        · simp only [Proc.f, HyperEnv.names_merge] at hFl ⊢
          rw [(Typing.f_eq_names hTP), (Typing.f_eq_names hTQ)] at hFl
          exact hFl
        · exact lwf
      · simp
    · apply Typing.mix ?_ hTP' hTQ'
      have := Typing.exchange_hyper hT hP
      have := Typing_preserves_disjointness this
      have hD := HyperEnv.disjoint_split this
      have := EnvStep.preserves_disjoint hStepP hD

      rw [Proc.f_par, (Typing.f_eq_names hTP), (Typing.f_eq_names hTQ)] at hFl
      rw [← Finset.disjoint_iff_inter_eq_empty] at hFl
      have hD_split := Finset.disjoint_union_right.mp hFl

      have hD𝒢'ℋ := EnvStep.preserves_disjoint
        hStepP hD (Disjoint.mono_left (by simp) hD_split.2)

      have hDl'𝒢': Disjoint (Lbl.act l').i ℋ₁'.names :=
        have : Disjoint (Lbl.act l').i (ℋ₁.names ∪ (Lbl.act l).i) := by
          rw [Finset.disjoint_union_right]
          constructor
          · exact Disjoint.mono_left (by simp) hD_split.1
          · symm
            simp only [Finset.disjoint_iff_inter_eq_empty]
            exact lwf
        Disjoint.mono_right (EnvStep.names_subset hStepP) this

      exact (EnvStep.preserves_disjoint hStepQ hD𝒢'ℋ.symm hDl'𝒢').symm



  case res => sorry

  case one_bot Q Q' L hQS ih =>
    obtain ⟨A, Γ, Δ, 𝒢, L', hP', hT'⟩ := Typing_inv_res hT
    obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh (L ∪ L')
    simp at hx hy
    obtain ⟨ℋ, hES, hTg⟩ := ih x hx.1 y hy.1 hneq (hT' x hx.2 y hy.2 hneq)


    use ℋ

    constructor
    · apply EnvStep.perm hP'.symm
      · apply EnvStep.one_bot (x := x) (y := y)
        sorry
      · sorry
    · exact hTg


  case tensor_parr => sorry



  case disp₁ x =>
    obtain ⟨Γ, A, hP', hT', hF⟩ := Typing_inv_disp₁ hT
    use [x ∶ ⊥ :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm EnvStep.disp₁ (by simp)
    · exact Typing.bot hF hT'

  case disp₂ P x =>
    obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
    use [x ∶ 1 :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm EnvStep.disp₂ (by simp)
    · have ⟨hNodup, _ ⟩:= Typing_preserves_linearity hT'
      have hNodupxΓ := hNodup (x ∶ A :: Γ) (by simp)
      obtain ⟨hxΓ, hNodupΓ⟩:= (Env.Nodup_cons.mp hNodupxΓ)
      have hNodup_names : ((P.f.erase x).toList).Nodup := Finset.nodup_toList _

      have heq : Env.names Γ = ((P.f.erase x).toList).toFinset := by
        ext a
        simp only [List.mem_toFinset, Finset.mem_toList, Finset.mem_erase]

        have hPf : P.f = Env.names (x ∶ A :: Γ) := by
          have := Typing.f_eq_names hT'
          simp only [HyperEnv.names_singleton] at this
          exact this

        rw [hPf]
        simp only [Env.names, List.map_cons, List.toFinset_cons, Finset.mem_insert]
        constructor
        · intro ha
          have h_neq : a ≠ x := by
            rintro rfl
            exact hxΓ ha
          exact ⟨h_neq, Or.inr ha⟩
        · rintro ⟨hneq, rfl | ha⟩
          · contradiction
          · exact ha

      have hlc : Env.lc n Γ := by
        have h_in_singleton : (x ∶ !!A :: Γ) ∈ [x ∶ !!A :: Γ] := by simp
        obtain ⟨Γ', hin𝒢, hP''⟩ := HyperEnv.Perm_mem hP' h_in_singleton
        have hlcΓ := Typing_preserves_lc_context hT Γ' hin𝒢
        have hlcAΓ := (Env.lc_perm hP'').mp hlcΓ
        have := (Env.lc_cons.mp hlcAΓ).2
        exact this

      exact Typing_buildDisp Γ _ hServ hNodup_names heq hxΓ hlc hNodupΓ

  case dup₁ x =>
    obtain ⟨Γ, A, L, hP', hF, hT'⟩ := Typing_inv_dup₁ hT
    use [x ∶ ??A ⅋ ??A :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm EnvStep.dup₁ (by simp)
    · apply Typing.parr ?_ (L ∪ {x})
      · simp at ⊢ hT'
        intros z hneq hin
        specialize hT' z hin hneq
        exact hT'
      · exact hF

  case dup₂ Q z =>
    obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
    use [z ∶ !!A ⨂ !!A :: Γ]
    · constructor
      · exact EnvStep.perm hP'.symm (EnvStep.dup₂ hServ) (by rfl)
      · apply Typing_buildDup (names := (Q.f.erase z).toList)
        · exact hServ
        · simp
          rw [Typing.f_eq_names hT']
          have hnd := (Typing_preserves_linearity hT').1
          simp [HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hnd
          exact hnd.1
        · exact Finset.nodup_toList _
        · exact hT'

  case use₁ x =>
    obtain ⟨Γ, A, hP', hT'⟩ := Typing_inv_use₁ hT
    use [x ∶ A :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm EnvStep.use₁ (by simp)
    · exact hT'

  case use₂ x =>
    obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
    use [x ∶ A :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm (EnvStep.use₂ hServ) (by simp)
    · exact hT'

  case output x A =>
    obtain ⟨Γ, B, hP', hT'⟩ := Typing_inv_output hT
    use [x ∶ B{A // 0} :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm EnvStep.output (by simp)
    · exact hT'

  case input x A hlc =>
    obtain ⟨Γ, B, hP', hT'⟩ := Typing_inv_input hT
    use [x ∶ B{A // 0} :: Γ]
    constructor
    · exact EnvStep.perm hP'.symm (EnvStep.input hlc) (by simp)
    · have := Typing_substTypes hT' (k := 0) (A := A)
      simp at this
      exact this (Types.lc_mono hlc)

  case selectL x =>
    obtain ⟨Γ, A, B, hP, hT⟩ := Typing_inv_selectL hT
    use [x ∶ A :: Γ]
    constructor
    · exact EnvStep.perm hP.symm EnvStep.selectL (by simp)
    · exact hT

  case selectR x =>
    obtain ⟨Γ, A, B, hP, hT⟩ := Typing_inv_selectR hT
    use [x ∶ B :: Γ]
    constructor
    · exact EnvStep.perm hP.symm EnvStep.selectR (by simp)
    · exact hT

  case ampL x =>
    obtain ⟨Γ, A, B, hP, hTP, hTQ⟩ := Typing_inv_amp hT
    use [x ∶ A :: Γ]
    constructor
    · exact EnvStep.perm hP.symm EnvStep.ampL (by simp)
    · exact hTP

  case ampR x =>
    obtain ⟨Γ, A, B, hP, hTP, hTQ⟩ := Typing_inv_amp hT
    use [x ∶ B :: Γ]
    constructor
    · exact EnvStep.perm hP.symm EnvStep.ampR (by simp)
    · exact hTQ

  case link₁ =>
    obtain ⟨A, hP⟩ := Typing_inv_link hT
    use ∅
    constructor
    · exact EnvStep.perm hP.symm (EnvStep.link₁) (by simp)
    · apply Typing.mix₀

  case link₂ x y =>
    obtain ⟨A, hP⟩ := Typing_inv_link hT
    use ∅
    constructor
    · have := HyperEnv.swap_two_inner (x := y) (y := x) (A := Aᗮᗮ) (B := Aᗮ)
      conv at this => rhs ; rw [Types.dual_involution]
      have := HyperEnv.Perm.trans hP this.symm
      apply EnvStep.perm this.symm
      · exact EnvStep.link₁
      · simp [HasPerm.perm]
    · apply Typing.mix₀

  case com => sorry
  case axcut => sorry
