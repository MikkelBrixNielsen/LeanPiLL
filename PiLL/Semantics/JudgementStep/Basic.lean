import PiLL.Semantics.Labels
import PiLL.Model.Judgement.Fresh

inductive TypingStepₘ : {n : Nat} → {𝒢 : HyperEnv} → {P : Proc} → Typing n P 𝒢 →
  Lbl → {n' : Nat} → {𝒢' : HyperEnv} → {P' : Proc} → Typing n' P' 𝒢' → Prop where
  | one
      {P : Proc} {x : FPName} {n : Nat} {𝒟 : Typing n P ∅} :
      TypingStepₘ (Typing.one (x := x) 𝒟) (x⟦⟧) 𝒟
  | bot
      {Γ : Env} {P : Proc} {x : FPName} {n : Nat} {hF : x ∉ Γ.names}
      {𝒟 : Typing n P [Γ]} :
      TypingStepₘ (Typing.bot (x := x) hF 𝒟) (x⸨⸩) 𝒟
  | tensor
      {Γ Δ : Env} {P : Proc} {x y : FPName} {A B : Types} {n : Nat}
      {hF: x ∉ Γ.names ∧ x ∉ Δ.names} {L : Finset FPName}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) ([z ∶ A :: Γ] |ₕ [x ∶ B :: Δ])}
      {hy : y ∉ ({x} ∪ P.f ∪ Γ.names ∪ Δ.names)} :
      TypingStepₘ (Typing.tensor hF L huniq) (x⟦y⟧) (Typing_tensor_all_fresh huniq y hy)
  | parr
      {Γ : Env} {P : Proc} {x y : FPName} {A B : Types} {n : Nat}
      {hF : x ∉ Γ.names} {L : Finset FPName}
      {huniq : ∀ z, z ∉ L → Typing n (P⸨#z⸩) [z ∶ A :: x ∶ B :: Γ]}
      {hy : y ∉ ({x} ∪ P.f ∪ Γ.names)} :
      TypingStepₘ (Typing.parr hF L huniq) (x⸨y⸩) (Typing_parr_all_fresh huniq y hy)
  | par₁
      {𝒢 ℋ 𝒢': HyperEnv} {P Q P' : Proc} {l : Lbl} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢'.disjoint ℋ}
      {𝒟 : Typing n P 𝒢} {𝒟' : Typing n P' 𝒢'} {ℰ : Typing n Q ℋ}
      (h : TypingStepₘ 𝒟 l 𝒟') (disj : (l.i) ∩ (Q.f) = ∅) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) l (Typing.mix hD2 𝒟' ℰ)
  | par₂
      {𝒢 ℋ ℋ': HyperEnv} {P Q Q' : Proc} {l : Lbl} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢.disjoint ℋ'}
      {𝒟 : Typing n P 𝒢} {ℰ : Typing n Q ℋ} {ℰ' : Typing n Q' ℋ'}
      (h : TypingStepₘ ℰ l ℰ') (disj : (l.i) ∩ (P.f) = ∅) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) l (Typing.mix hD2 𝒟 ℰ')
  | syn
      {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' Q Q' : Proc} {l l' : Act} {n : Nat}
      {hD1 : 𝒢.disjoint ℋ} {hD2 : 𝒢'.disjoint ℋ'}
      {𝒟 : Typing n P 𝒢} {𝒟' : Typing n P' 𝒢'}
      {ℰ : Typing n Q ℋ} {ℰ' : Typing n Q' ℋ'}
      (h₁ : TypingStepₘ 𝒟 l 𝒟') (h₂ : TypingStepₘ ℰ l' ℰ')
      (disj : (l |ₗ l').i ∩ (P |ₚ Q).f = ∅)
      (WF : (l |ₗ l').WF) :
      TypingStepₘ (Typing.mix hD1 𝒟 ℰ) (l |ₗ l') (Typing.mix hD2 𝒟' ℰ')
| one_bot
      {𝒢 𝒢' : HyperEnv} {Γ : Env} {P P' : Proc} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
        Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ 1 :: ∅] |ₕ [y ∶ ⊥ :: Γ])}
      {x y : FPName}
      {hx : x ∉ ({y} ∪ P.f ∪ 𝒢.names ∪ Γ.names)}
      {hy : y ∉ (P.f ∪ 𝒢.names ∪ Γ.names)}
      {𝒟' : Typing n P' (𝒢 |ₕ [∅‚ Γ])}
      (hStep : TypingStepₘ (Typing_one_bot_all_fresh huniq x y hx hy) (x⟦()⟧ |ₗ y⸨()⸩) 𝒟') :
      TypingStepₘ (Typing.cut L huniq) (τ) 𝒟'
| tensor_parr
      {𝒢 : HyperEnv} {Γ Δ Ξ : Env} {P P' : Proc} {A B : Types} {n : Nat} {L : Finset FPName}
      {huniq : ∀ x ∉ L, ∀ y ∉ L, x ≠ y →
        Typing n
          (P⸨#x, #y⸩)
          (𝒢 |ₕ [x ∶ A ⨂ B :: Γ‚ Δ] |ₕ [y ∶ Aᗮ ⅋ Bᗮ :: Ξ])}
      {huniq' : ∀ x ∉ L, ∀ y ∉ L, x ≠ y → ∀ x' ∉ L, ∀ y' ∉ L, x' ≠ y' →
        x ≠ x' → x ≠ y' → y ≠ x' → y ≠ y' →
        Typing n
          (P'⸨2 | #x, #y⸩⸨#x', #y'⸩)
          (𝒢 |ₕ [x ∶ B :: Δ] |ₕ [x' ∶ A :: Γ] |ₕ [y' ∶ Aᗮ :: y ∶ Bᗮ :: Ξ])}
      {x y : FPName} (hx : x ∉ L) (hy : y ∉ L) (hneq : x ≠ y)
      {x' y' : FPName} (hx' : x' ∉ L) (hy' : y' ∉ L) (hneq' : x' ≠ y')
      (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x') (hyy' : y ≠ y')
      (hxP : x ∉ P.f) (hyP : y ∉ P.f) (hx'P : x' ∉ P.f) (hy'P : y' ∉ P.f)
      (hxP' : x ∉ P'.f) (hyP' : y ∉ P'.f) (hx'P' : x' ∉ P'.f) (hy'P' : y' ∉ P'.f)
      (hStep : TypingStepₘ (huniq x hx y hy hneq) (x⟦x'⟧ |ₗ y⸨y'⸩)
        (huniq' x hx y hy hneq x' hx' y' hy' hneq' hxx' hxy' hyx' hyy')) :
      TypingStepₘ
        (Typing.cut L huniq)
        (τ)
        (Typing_double_cut_tensor_parr huniq')
| res
      {𝒢 𝒢' : HyperEnv} {Γ Γ' Δ Δ' : Env} {P P' : Proc} {A : Types} {n : Nat} {l : Lbl}
      {L L' : Finset FPName}
      {huniq : ∀ z ∉ L, ∀ w ∉ L, z ≠ w →
        Typing n (P⸨#z, #w⸩) (𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ Aᗮ :: Δ])}
      {huniq' : ∀ z ∉ L', ∀ w ∉ L', z ≠ w →
        Typing n (P'⸨#z, #w⸩) (𝒢' |ₕ [z ∶ A :: Γ'] |ₕ [w ∶ Aᗮ :: Δ'])}
      {x y : FPName} (hneq : x ≠ y)
      (hx_pre : x ∉ P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names)
      (hy_pre : y ∉ P.f ∪ 𝒢.names ∪ Γ.names ∪ Δ.names)
      (hx_post : x ∉ P'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names)
      (hy_post : y ∉ P'.f ∪ 𝒢'.names ∪ Γ'.names ∪ Δ'.names)
      (hlx : x ∉ l.f ∪ l.i) (hly : y ∉ l.f ∪ l.i)
      (hStep : TypingStepₘ
        (Typing_res_all_fresh huniq x y hx_pre hy_pre hneq) l
        (Typing_res_all_fresh huniq' x y hx_post hy_post hneq)) :
      TypingStepₘ (Typing.cut L huniq) l (Typing.cut L' huniq')
  ------- Additional Structural / Exchange Rules -------
  | perm_env {𝒢 ℋ : HyperEnv} {Γ Γ' : Env} {P P' : Proc} {n n' : Nat} {l : Lbl}
    {𝒟 : n ⊢ P ∷ (Γ :: 𝒢)} {𝒟' : n' ⊢ P' ∷ ℋ} (hP1 : Γ ~ Γ')
    (hTS : TypingStepₘ 𝒟 l 𝒟') :
    TypingStepₘ (Typing.exchange_env 𝒟 hP1) l 𝒟'
  | perm_hyper {𝒢 𝒢' ℋ ℋ' : HyperEnv} {P P' : Proc} {n n' : Nat} {l : Lbl}
    {𝒟 : n ⊢ P ∷ 𝒢} {𝒟' : n' ⊢ P' ∷ ℋ} (hP1 : 𝒢 ~ 𝒢') (hP2 : ℋ ~ ℋ')
    (hTS : TypingStepₘ 𝒟 l 𝒟') :
    TypingStepₘ (Typing.exchange_hyper 𝒟 hP1) l (Typing.exchange_hyper 𝒟' hP2)

instance {n n' : Nat} {𝒢 𝒢' : HyperEnv} {P P' : Proc} :
  HasStep (Typing n P 𝒢) Lbl (Typing n' P' 𝒢') where
  step 𝒟 l 𝒟' := TypingStepₘ 𝒟 l 𝒟'
