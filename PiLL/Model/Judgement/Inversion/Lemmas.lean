import PiLL.Model.Judgement.Basic
import PiLL.Model.HyperEnvironment.Lemmas.Basic

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
    simp only [Proc.one.injEq, Channel.free.injEq] at heq
    constructor
    · rw [heq.1]
    · rw [heq.2] ; exact hT

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
    simp only [Proc.bot.injEq, Channel.free.injEq] at heq
    constructor
    · constructor
      · rw [heq.1]
      · rw [heq.2]
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
  case tensor Γ Δ _ _ A B _ _ L hT _ =>
    simp only [Proc.tensor.injEq, Channel.free.injEq] at heq
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
  case parr Γ _ _ A B _ _ L hT _ =>
    simp only [Proc.parr.injEq, Channel.free.injEq] at heq
    use A, B, Γ, L
    constructor
    · rw [heq.1]
    · rw [heq.1, heq.2]
      exact hT

lemma Typing_inv_par {n : Nat} {P Q : Proc} {𝒢 : HyperEnv} (hT : n ⊢ P |ₚ Q ∷ 𝒢) :
  ∃ 𝒢₁ 𝒢₂, (𝒢 ~ 𝒢₁ |ₕ 𝒢₂) ∧ (n ⊢ P ∷ 𝒢₁) ∧ (n ⊢ Q ∷ 𝒢₂) ∧ Disjoint 𝒢₁.names 𝒢₂.names := by
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
  case mix 𝒢 ℋ _ _ _ hD hTP hTQ ihP ihQ =>
    simp only [Proc.par.injEq] at heq
    obtain ⟨hP, hQ⟩ := heq
    use 𝒢, ℋ
    rw [hP, hQ]
    exact ⟨by simp, hTP, hTQ, hD⟩

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
    simp only [Proc.link.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.amp.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.selectL.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.selectR.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.output.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.input.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.consume.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.server.injEq, Channel.free.injEq, Finset.empty_eq_image] at heq
    obtain ⟨rfl, _, rfl⟩ := heq
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
    simp only [Proc.dispose.injEq, Channel.free.injEq] at heq
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
    simp only [Proc.duplicate.injEq, Channel.free.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    use Γ, A, L
    constructor
    · simp
    · constructor
      · exact hF
      · intros x' hin hneq
        apply Typing.exchange_hyper (hT x' hin)
        exact HyperEnv.Perm.cons (List.Perm.swap (x' ∶ ??A) (x ∶ ??A) Γ) (by simp)

lemma Typing_inv_res {n : Nat} {P : Proc} {𝒢 : HyperEnv}
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
      exact hT x hx y hy hneq
