import PiLL.Model.HyperEnvironment.Basic
import PiLL.Model.Processes.OpenClose
import PiLL.Model.Processes.Notation
import PiLL.Model.STypes.Notation

inductive Typing : Nat → Proc → HyperEnv → Prop where
  ----------------- Actual Typing Rules -----------------
  | mix₀ {n : Nat} :
      Typing n 𝟘 ∅
  | mix {𝒢 ℋ : HyperEnv} {P Q : Proc} {n : Nat} (hD : 𝒢.disjoint ℋ) :
      Typing n P 𝒢 → Typing n Q ℋ →
      ------------------------------
      Typing n (P |ₚ Q) (𝒢 |ₕ ℋ)
  | one {P : Proc} {x : FPName} {n : Nat} :
      Typing n P ∅ →
      ---------------------------
      Typing n (#x⟦⟧․P) [[x ∶ 1]]
  | bot {Γ : Env} {P : Proc} {x : FPName} {n : Nat} (hF : x ∉ Γ.names) :
      Typing n P [Γ] →
      ------------------------------
      Typing n (#x⸨⸩․P) [x ∶ ⊥ :: Γ]
  | cut {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {A : Types} {n : Nat} (L : Finset FPName) :
      (∀ x ∉ L, ∀ y ∉ L, x ≠ y →
      Typing n (P⸨#x, #y⸩) (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ])) →
      ----------------------------------------------------------
      Typing n (𝑣⸨$N,$N⸩ P) (𝒢 |ₕ [Γ‚ Δ])
  | tensor {Γ Δ : Env} {P : Proc} {x : FPName} {A B : Types}
      {n : Nat} (hF : x ∉ Γ.names ∧ x ∉ Δ.names) (L : Finset FPName) :
      (∀ y ∉ L, Typing n (P⸨#y⸩) ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])) →
      ---------------------------------------------------------------
      Typing n (#x⟦$N⟧․P) [x ∶ A ⨂ B :: Γ‚ Δ]
  | parr {Γ : Env} {P : Proc} {x : FPName} {A B : Types}
      {n : Nat} (hF : x ∉ Γ.names) (L : Finset FPName) :
      (∀ y ∉ L, Typing n (P⸨#y⸩) [y ∶ A :: x ∶ B :: Γ]) →
      -------------------------------------------------------
      Typing n (#x⸨$N⸩․P) [x ∶ A ⅋ B :: Γ]
  | oplus₁
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      B.lc n →
      Typing n P [x ∶ A :: Γ] →
      -----------------------------------
      Typing n (#x⟦𝐋⟧․P) [x ∶ A ⊕ B :: Γ]
  | oplus₂
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      A.lc n →
      Typing n P [x ∶ B :: Γ] →
      ------------------------------------
      Typing n (#x⟦𝐑⟧․P) [x ∶ A ⊕ B :: Γ]
  | amp
      {Γ : Env} {P Q : Proc} {x : FPName} {A B : Types} {n : Nat} :
      Typing n P [x ∶ A :: Γ] → Typing n Q [x ∶ B :: Γ] →
      ---------------------------------------------------
      Typing n (#x․case{𝐋 : P, 𝐑 : Q}) [x ∶ A & B :: Γ]
  | quest
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} :
      Typing n P [x ∶ A :: Γ] →
      -----------------------------------
      Typing n (#x⟦USE⟧․P) [x ∶ ??A :: Γ]
  | bang
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} :
      ?ₑΓ → Typing n P [x ∶ A :: Γ] →
      -----------------------------------------------------------
      Typing n (!#x⟨Γ.names.image Channel.free⟩․{P}) [x ∶ !!A :: Γ]
  | w
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat} (hF : x ∉ Γ.names) :
      A.lc n → Typing n P [Γ] →
      -----------------------------------
      Typing n (#x⟦DISP⟧․P) [x ∶ ??A :: Γ]
  | c
      {Γ : Env} {P : Proc} {x : FPName} {A : Types} {n : Nat}
      (hF : x ∉ Γ.names) (L : Finset FPName) :
      (∀ x' ∉ L, Typing n P⸨#x'⸩ [x ∶ ??A :: x' ∶ ??A :: Γ]) →
      -------------------------------------------------------------
      Typing n (#x⟦DUP⟧⸨$N⸩․P) [x ∶ ??A :: Γ]
  | exists_
      {Γ : Env} {P : Proc} {x : FPName} {A B : Types} {n : Nat} :
      A.lc n →
      Typing n P [x ∶ B{A // 0} :: Γ] →
      ----------------------------------
      Typing n (#x⟦A⟧․P) [x ∶ ∃․B :: Γ]
  | forall_
      {Γ : Env} {P : Proc} {x : FPName} {B : Types} {n : Nat} :
      Typing (n + 1) P [x ∶ B :: Γ⁺ᵗ] →
      ----------------------------------
      Typing n (#x⸨$T⸩․P) [x ∶ ∀․B :: Γ]
  | ax
      {x y : FPName} {A : Types} {n : Nat} (hneq : x ≠ y):
      A.lc n →
      Typing n (#x ⟷ₚ #y) [x ∶ Aᗮ :: [y ∶ A]]
  ------- Additional Structural / Exchange Rules -------
  | exchange_env {𝒢 : HyperEnv} {Γ Δ : Env} {P : Proc} {n : Nat} :
      Typing n P (Γ :: 𝒢) → Γ ~ Δ →
      -----------------------------
      Typing n P (Δ :: 𝒢)
  | exchange_hyper {𝒢 ℋ : HyperEnv} {P : Proc} {n : Nat} :
      Typing n P 𝒢 → 𝒢 ~ ℋ →
      -----------------------
      Typing n P ℋ

notation:50 n " ⊢ " P " ∷ " 𝒢 => Typing n P 𝒢

-- Projection of a Judgement to its process
def proc {𝒢 : HyperEnv} {P : Proc} {n : Nat} (_ : n ⊢ P ∷ 𝒢) : Proc := P

-- Projection of a Judgement to its environment
def env {𝒢 : HyperEnv} {P : Proc} {n : Nat} (_ : n ⊢ P ∷ 𝒢) : HyperEnv := 𝒢
