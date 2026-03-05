import PiLL.Framework.Semantics.EnvStep
import PiLL.Framework.Semantics.ProcStep
import PiLL.Framework.Substitution








-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr

-- FIXME: Move exchange rules to the bottom of Typing, revise substNames / Types
--        Can probably combine a lot of cases using constructor doing this

-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere
-- FIXME: Check possibility of removing exchange_env typing rule



-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs
-- FIXME: Check possibility of no having exchange rules
-- FIXME: Find different syntax for open?

-- FIXME: Proof of HyperEnv.names only having free names
-- FIXME: Proof that HyperEnv.names = Proc.f
-- FIXME: Something regarding Name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }


-- FIXME: Lemma : n ⊢ P ∷ 𝒢 → (P.f = 𝒢.names)




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





@[simp] lemma Env.names_nil :
  Env.names [] = ∅ := by simp [Env.names]

@[simp] lemma Env.names_singleton {x : FPName} {A : Types} :
  Env.names [x ∶ A] = {x} := by simp [Env.names]

@[simp] lemma Env.names_distributes {Γ : Env} {x : FPName} {A : Types} :
  Env.names (x ∶ A :: Γ) = {x} ∪ Γ.names := by simp [Env.names]

@[simp] lemma Env.names_merge {Γ Δ : Env} :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by simp [Env.names]


@[simp] lemma HyperEnv.names_nil :
  HyperEnv.names [] = ∅ := by simp [HyperEnv.names]

@[simp] lemma HyperEnv.names_singleton (Γ : Env) :
  HyperEnv.names [Γ] = Γ.names := by
  simp [HyperEnv.names, Env.names, List.foldr]

@[simp] lemma HyperEnv.names_distributes {𝒢 : HyperEnv} {Γ : Env} :
  HyperEnv.names (Γ :: 𝒢) = Γ.names ∪ 𝒢.names := by simp [HyperEnv.names, Env.names]

@[simp] lemma HyperEnv.names_merge (𝒢 ℋ : HyperEnv) :
  (𝒢 |ₕ ℋ).names = 𝒢.names ∪ ℋ.names := by
  induction 𝒢
  case nil => simp [HyperEnv.names]
  case cons _ _ ih => simp ; rw [ih]



lemma HyperEnv.names_eq_of_perm {𝒢 ℋ : HyperEnv} (h : 𝒢 ~ ℋ) :
  𝒢.names = ℋ.names := by
  induction h with
  | nil => simp
  | cons hPE _ ih => simp ; rw [Env.names_eq_of_perm hPE, ih]
  | swap Γ Δ => simp ; rw [← Finset.union_assoc, Finset.union_comm Γ.names _, Finset.union_assoc]
  | trans _ _ ih1 ih2 => apply Eq.trans ih1 ih2





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

  case parr Γ P x _ _ _ _ L _ ih | c Γ P x _ _ L _ ih =>
    have ⟨y, hy⟩ := exists_one_fresh (L ∪ P.f ∪ {x} ∪ Γ.names)
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






lemma typing_inv_one {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⟦⟧․P) 𝒢) :
  (𝒢 ~ [[x ∶ 1]]) ∧ Typing n P ∅ := by
  generalize heq : (#x⟦⟧․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨h1, h2⟩ := ih (P := P) (x := x) heq
    have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
    exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨h1, h2⟩ := ih (P := P) (x := x) heq
    exact ⟨HyperEnv.Perm.trans hP.symm h1, h2⟩

  case one hT _ =>
    simp at heq
    constructor
    · simp [heq.1, HasPerm.perm]
    · simp [heq.2]
      exact hT

lemma typing_inv_bot {n : Nat} {P : Proc} {x : FPName} {𝒢 : HyperEnv}
  (hT : Typing n (#x⸨⸩․P) 𝒢) :
  ∃ Γ, (𝒢 ~ [x ∶ ⊥ :: Γ]) ∧ Typing n P [Γ] := by
  generalize heq : (#x⸨⸩․P) = P' at hT
  induction hT generalizing P x <;> try contradiction

  case exchange_env ℋ _ _ _ _ _ hP ih =>
    have ⟨Ξ, h⟩ := ih (P := P) (x := x) heq
    obtain ⟨h1, h2⟩ := h
    constructor
    · have := HyperEnv.Perm.cons hP.symm (HyperEnv.Perm.refl ℋ)
      exact ⟨HyperEnv.Perm.trans this h1, h2⟩

  case exchange_hyper hP ih =>
    have ⟨Γ, h⟩ := ih (P := P) (x := x) heq
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

lemma typing_inv_tensor {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⟦$N⟧․P) 𝒢) :
  ∃ (A B : Types) (Γ Δ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⨂ B :: Γ‚ Δ]) ∧
    (∀ z ∉ L, Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) := by
  generalize heq : (#x⟦$N⟧․P) = P' at hT
  induction hT generalizing P <;> try contradiction

  case exchange_env 𝒢' _ _ _ _ _ hP ih =>
    obtain ⟨A, B, Γ, Δ, L, hP', hT⟩ := ih (P := P) heq
    use A, B, Γ, Δ, L

    constructor
    · have h_cong : Δ :: 𝒢' ~ Γ :: 𝒢' := by sorry


      sorry
    · exact hT

  case exchange_hyper ih =>
    sorry

  case tensor ih =>
    sorry


lemma typing_inv_parr {n : Nat} {P : Proc} {𝒢 : HyperEnv} {x : FPName}
  (hT : Typing n (#x⸨$N⸩․P) 𝒢) :
  ∃ (A B : Types) (Γ : Env) (L : Finset FPName),
    (𝒢 ~ [x ∶ A ⅋ B :: Γ]) ∧
    (∀ z ∉ L, Typing n (P⸨#z⸩) ([x ∶ B :: z ∶ A :: Γ])) := by
  generalize heq : (#x⸨$N⸩․P) = P' at hT
  induction hT generalizing P <;> try contradiction
  all_goals sorry




-- FIXME: Check that this covers all rules mentioned in the paper
-- FIXME: Subject reduction / simulation proof
theorem session_fidelity {n : Nat} {P P' : Proc} {𝒢 : HyperEnv} {l : Lbl} :
  Typing n P 𝒢 → ProcStep P l P' →
  ∃ 𝒢', EnvStep 𝒢 l 𝒢' ∧ Typing n P' 𝒢' := by
  intros hT hPS
  induction hPS generalizing n 𝒢

  case one =>
    obtain ⟨hP, 𝒟⟩ := typing_inv_one hT
    use ∅
    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.one
      · exact HyperEnv.Perm.nil
    · exact 𝒟

  case bot =>
    obtain ⟨Γ, hP, 𝒟⟩ := typing_inv_bot hT
    use [Γ]
    constructor
    · apply EnvStep.perm hP.symm
      · exact EnvStep.bot
      · apply HyperEnv.Perm.refl
    · exact 𝒟

  case tensor Q x y hF =>
    obtain ⟨A, B, Γ, Δ, L, hP, 𝒟⟩ := typing_inv_tensor hT
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
    obtain ⟨A, B, Γ, L, hP, 𝒟⟩ := typing_inv_parr hT
    use [x ∶ B :: y ∶ A :: Γ]

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
          case head => rfl
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






-- 2nd april påskefrokost Bolderslev
-- 5th april påskefrokost København












  all_goals sorry
