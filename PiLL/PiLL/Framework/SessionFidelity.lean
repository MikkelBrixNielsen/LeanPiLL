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
    obtain ⟨Γ, A, hP', hT'⟩:= ih heq
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
    (𝒢 ~ [x ∶ ??A :: Γ]) ∧
    x ∉ Γ.names ∧
    (∀ x' ∉ L, x' ≠ x → n ⊢ P⸨#x'⸩ ∷ [x' ∶ ??A :: x ∶ ??A :: Γ]) := by
  generalize heq : (#x⟦DUP⟧⸨$N⸩․P) = Pdup at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env hP ih =>
    obtain ⟨Γ, A, x', hP', hT'⟩:= ih heq
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






-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr

-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere
-- FIXME: Check possibility of removing exchange_env typing rule



-- FIXME: proof of Typing n P 𝒢 → 𝒢 is pairwise disjoint and nodup


-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs
-- FIXME: Find different syntax for open?
-- FIXME: Prove name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }




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

lemma Typing_buildDup_aux' {n : Nat} {P : Proc} {x : FPName} {A : Types}
  (names : List FPName) (acc : List FPName) (Γ : Env) (hT : n ⊢ P ∷ [x ∶ A :: Γ])
  (hServ : ?ₑΓ) (hNodup : names.Nodup) (heq : Γ.names = names.toFinset)
  (hxΓ : x ∉ Γ.names) (hlc : Γ.lc n) (hNodupΓ : Env.Nodup Γ) :
  n ⊢ wrapDup (#x⟦$N⟧․closeAll (!(#x)⟪x⟫․{P⟪x⟫}) 1 acc.reverse |ₚ !#x․{P}) names ∷
    [x ∶ !!A ⨂ !!A :: Γ] := by
  induction names generalizing Γ acc

  case nil =>
    simp [wrapDup]
    simp [Env.names] at heq
    subst heq
    apply Typing.tensor (Γ := []) (L := {x}) (by simp)
    intro y hy
    simp only [Proc.open_par]
    have hFy : y ∉ P.f := by simp [Typing.f_eq_names hT, hy]
    have hlc' := Typing_preserves_lc hT
    apply Typing.mix
    · simp [← ne_eq] at hy ⊢
      exact hy.symm
    · have hPf := Typing.f_eq_names hT
      have hSE : (!$0․{P⟪x⟫}).f = ∅ := by simp [hPf]
      have hTy := Typing_substNames (x := x) (y := y) hT (by simp)
      simp [Proc.closeAll_not_mem hSE]
      rw [Proc.close_open_eq_substNames hFy hlc'.1]
      exact Typing.bang (by simp) (by simp at hTy ; exact hTy)
    · rw [Proc.open_lc_0]
      · exact Typing.bang (by simp) hT
      · simp [Channel.f] at ⊢ hy
        exact ⟨hy, hFy⟩
      · simp [Proc.lc, Channel.lc] ; exact hlc'.1

  case cons y names ih => sorry





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


lemma Proc.closeAll_open_subst {P : Proc} {names : List FPName} {y z : FPName} {k n : Nat}
  (hF : z ∉ P.f) (hlc : lc k n P):
  (closeAll P k (names ++ [y]))⸨k + names.length | #z⸩ = closeAll (P{z // y}) k names := by
  induction names generalizing k
  case nil =>
    simp [closeAll]
    rw [Proc.close_open_eq_substNames]
    · exact hF
    · exact hlc

  case cons z zs ih =>
    simp [closeAll]
    sorry



lemma Typing_buildDup_aux {n : Nat} {Q : Proc} {x : FPName} {A : Types}
  (names : List FPName) (Γ_curr : Env)

  -- Q is our active server, typed by the shrinking environment!
  (hT_Q : n ⊢ Q ∷ [x ∶ A :: Γ_curr])
  (hEq : Γ_curr.names = names.toFinset)

  -- Structural properties
  (hServ : ?ₑΓ_curr) (hx : x ∉ Γ_curr.names)
  (hNodup : Γ_curr.Nodup) (hlc : Env.lc n Γ_curr) :

  -- Notice both wrapDup and closeAll use EXACTLY `names`
  n ⊢ wrapDup (#x⟦$N⟧․closeAll (!(#x)⟪x⟫․{Q⟪x⟫}) 1 names.reverse |ₚ !#x․{Q}) names ∷
      [x ∶ !!A ⨂ !!A :: Γ_curr] := by

  -- We generalize Q, because Q will accumulate substitutions!
  -- induction names generalizing Γ_curr Q
  sorry























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
      simp [← Proc.open_subst_intro (z := y) hz4] at 𝒟'

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

      rw [← Proc.open_subst_intro] at 𝒟'
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
      · exact EnvStep.par₁ hStep
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
      · exact EnvStep.par₂ hStep
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
    · exact EnvStep.perm hP.symm (EnvStep.syn hStepP hStepQ lwf) (by simp)
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
  case one_bot => sorry
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




    sorry

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
