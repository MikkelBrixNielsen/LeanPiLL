import PiLL.Model.Environment.Basic
import PiLL.Model.Processes.SubstNames
import PiLL.Model.Processes.SubstTypes
import PiLL.Model.Processes.LocalClosure
import PiLL.Model.STypes.Lemmas

@[simp] lemma Env.names_nil :
  Env.names [] = ∅ := by simp [Env.names]

@[simp] lemma Env.names_singleton {x : FPName} {A : Types} :
  Env.names [x ∶ A] = {x} := by simp [Env.names]

@[simp] lemma Env.names_distributes {Γ : Env} {x : FPName} {A : Types} :
  Env.names (x ∶ A :: Γ) = {x} ∪ Γ.names := by simp [Env.names]

@[simp] lemma Env.names_merge {Γ Δ : Env} :
  (Γ‚ Δ).names = Γ.names ∪ Δ.names := by simp [Env.names]

@[simp] lemma Env.mem_pair_fst_in_names_iff {Γ : Env} {x : FPName} :
   x ∈ Γ.names ↔ ∃ A, (x, A) ∈ Γ := by simp_all [Env.names]

@[simp] lemma Env.mem_pair_fst_in_names {Γ : Env} {x : FPName} :
   ∀ A, (x, A) ∈ Γ → x ∈ Γ.names := by
   intro A hin
   cases hin
   case head => simp_all [Env.mem_pair_fst_in_names_iff]
   case tail hd tl hin =>
    simp_all [Env.mem_pair_fst_in_names_iff]
    use A
    exact Or.inr hin

@[simp] lemma Env.not_mem_names_iff {Γ : Env} {x : FPName} :
  x ∉ Γ.names ↔ ∀ A, (x, A) ∉ Γ := by
  simp [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.not_mem_names_cons {Γ : Env} {E : Elem} {x : FPName} :
  x ∉ Env.names (E :: Γ) ↔ x ≠ E.1 ∧ x ∉ Γ.names := by
  simp_all
  constructor
  · intro h
    simp_all
    obtain ⟨E1, E2⟩ := E
    specialize h E2
    simp_all
  · intro A
    obtain ⟨E1, E2⟩ := E
    simp_all

@[simp] lemma Env.Perm.nil :
  ([] : Env) ~ ([] : Env) := by simp [HasPerm.perm]

@[simp, refl] lemma Env.Perm.refl (Γ : Env) : Γ ~ Γ := by
  simp [HasPerm.perm]

lemma Env.Perm.rfl {Γ : Env} : Γ ~ Γ := .refl _

lemma Env.Perm.symm {Γ Δ : Env} (hP : Γ ~ Δ) : Δ ~ Γ := by
  simp [HasPerm.perm] at ⊢ hP ; exact hP.symm

lemma Env.Perm.comm {Γ Δ : Env} : Γ ~ Δ ↔ Δ ~ Γ :=
  ⟨Env.Perm.symm, Env.Perm.symm⟩

lemma Env.Perm.cons {a : Elem} {Γ Δ : Env} : Γ ~ Δ → (a :: Γ) ~ (a :: Δ) := by
  simp [HasPerm.perm]

lemma Env.Perm.swap {a b : Elem} {Γ : Env} : (a :: b :: Γ) ~ (b :: a :: Γ) := by
  simp [HasPerm.perm] ; apply List.Perm.swap

lemma Env.Perm.trans {Γ Δ Ξ : Env} : Γ ~ Δ → Δ ~ Ξ → Γ ~ Ξ := by
  simp [HasPerm.perm] ; intros h1 h2 ; exact List.Perm.trans h1 h2

lemma Env.Perm.merge_rotate_left (Γ : Env) (x : FPName × Types) :
  (x :: Γ).Perm (Γ‚ [x]) := by
  symm ; apply List.perm_append_singleton

lemma Env.Perm.merge_swap (Γ : Env) (x y : FPName × Types) :
  List.Perm (x :: y :: Γ) (y :: x :: Γ) := by
  symm ; simpa using List.Perm.swap x y Γ

lemma Env.names_eq_of_perm {Γ Δ : Env} (h : Γ ~ Δ) :
  Γ.names = Δ.names := by
  dsimp [Env.names]
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset]
  apply List.Perm.mem_iff
  apply List.Perm.map _ h

lemma Env.Perm.eq_nil_of_disjoint {Γ Δ : Env} (hD : Γ.disjoint Δ) (hP : Γ.Perm Δ) :
  Γ = [] ∧ Δ = [] := by
  induction hP
  case nil => simp
  case cons E Γ Δ hP ih =>
    rcases E with ⟨x, A⟩
    simp only [disjoint, names_distributes, Finset.singleton_union,
      Finset.disjoint_insert_right, Finset.mem_insert, true_or,
      not_true_eq_false, Finset.disjoint_insert_left,false_and] at hD
  case swap E1 E2 Γ => rcases E1 ; rcases E2 ; simp at hD
  case trans l1 l2 l3 hP1 hP2 ih1 ih2 =>
    simp [Disjoint] at hD
    have hNamesEq := Env.names_eq_of_perm (hP1.trans hP2)
    have hEmptyNames : names l1 = ∅ := by
      apply hD (x := names l1)
      · simp only [subset_refl]
      · rw [← hNamesEq]
    have h1 : l1 = [] := by simp_all
    have h2 : l3 = [] := by simp_all
    refine ⟨h1, h2⟩

@[simp] lemma Env.Perm.swap_two {x y : FPName} {A B : Types} :
  [x ∶ A, y ∶ B] ~ [y ∶ B, x ∶ A] := by
  exact List.Perm.swap ..

lemma Env.perm_disjoint {Γ Δ Ξ : Env} (hP : Γ ~ Δ) :
  Γ.disjoint Ξ ↔ Δ.disjoint Ξ := by
  simp [Env.disjoint]
  rw [← Env.names_eq_of_perm hP]

lemma Env.disjoint_symm {Γ Δ : Env} : Env.disjoint Γ Δ ↔ Env.disjoint Δ Γ := by
  exact disjoint_comm

lemma Env.mem_of_disjoint_le_bot {Γ Δ : Env} {x : Finset FPName}
  (hΓΔ : Disjoint Γ.names Δ.names) (hxΓ : x ≤ Γ.names) (hxΔ : x ≤ Δ.names) :
  x ≤ ⊥ := by
  exact le_trans (le_inf hxΓ hxΔ) (Disjoint.le_bot hΓΔ)

lemma Env.disjoint_cons_iff {Γ Δ : Env} {x y : FPName} {A : Types} :
  Disjoint (Env.names (x ∶ A :: Γ)) (Env.names (y ∶ Aᗮᗮ :: Δ)) ↔
  (y ≠ x ∧ y ∉ Γ.names ∧ x ∉ Δ.names ∧ Disjoint Γ.names Δ.names) := by
  simp only [Env.names_distributes, Finset.singleton_union, Finset.disjoint_insert_right,
    Finset.mem_insert, not_or, ← ne_eq, Finset.disjoint_insert_left]
  constructor
  · intro h
    rcases h with ⟨⟨hneq, hyΓ⟩, ⟨hxΔ, hDΓΔ⟩⟩
    refine ⟨hneq, hyΓ, hxΔ, hDΓΔ⟩
  · intro h
    rcases h with ⟨hneq, hyΓ, hxΔ, hDΓΔ⟩
    refine ⟨⟨hneq, hyΓ⟩, ⟨hxΔ, hDΓΔ⟩⟩

lemma Env.lc_shift_inv {n k : Nat} {Γ : Env} :
  (Γ⁺).lc (n + k + 1) ↔ Γ.lc (n + k) := by
  simp [Env.lc, HasShift.shift, Env.shiftTypes]
  constructor
  all_goals (
    intro h x A hin
    specialize h x A hin
    have := Types.lc_shift_inv_0 (A := A) (n := n + k)
    simp_all
  )

lemma Env.lc_shift_inv_0 {n : Nat} {Γ : Env} :
  (Γ⁺).lc (n + 1) ↔ Γ.lc n := Env.lc_shift_inv (k := 0)

@[simp] lemma Env.lc_nil {n : Nat} :
  Env.lc n ([] : Env) := by simp [Env.lc]

lemma Env.lc_cons {n : Nat} {x : FPName} {A : Types} {Γ : Env} :
  Env.lc n ((x, A) :: Γ) ↔ A.lc n ∧ Γ.lc n := by
  unfold Env.lc
  constructor
  · intro h
    constructor
    · apply h x A
      simp
    · intro y B hΓ
      apply h y B
      simp [hΓ]
  · rintro ⟨h1, h2⟩ y B hMem
    cases hMem
    · exact h1
    · rename_i hΓ
      apply h2 y B hΓ

lemma Env.lc_singleton {n : Nat} {x : FPName} {A : Types} :
  Env.lc n ([x ∶ A]) ↔ A.lc n := by simp_all [Env.lc]

lemma Env.lc_append {n : Nat} {Γ Δ : Env} :
  (Γ‚ Δ).lc n ↔ Γ.lc n ∧ Δ.lc n := by
  simp [Env.lc, Env.merge]
  constructor
  · intro h
    constructor
    · intro x A hin
      exact h x A (Or.inl hin)
    · intro x A hin
      exact h x A (Or.inr hin)
  · intro ⟨hΓ, hΔ⟩ x A hin
    cases hin with
    | inl hin => exact hΓ x A hin
    | inr hin => exact hΔ x A hin

lemma Env.lc_perm {n : Nat} {Γ Δ : Env} :
  Γ ~ Δ → (Γ.lc n ↔ Δ.lc n) := by
  intro hPerm
  simp [Env.lc]
  constructor
  · intro h x A hin
    rw [List.Perm.mem_iff hPerm.symm] at hin
    exact h x A hin
  · intro h x A hin
    rw [List.Perm.mem_iff hPerm] at hin
    exact h x A hin

@[simp] lemma Env.substNames_singleton {x y : FPName} {A : Types} :
  ([x ∶ A] : Env){y // x} = [x{y // x} ∶ A] := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]

@[simp] lemma Env.substNames_distributes {Γ : Env} {x y z : FPName} {A : Types} :
  (z ∶ A :: Γ){y // x} = z{y // x} ∶ A :: Γ{y // x} := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]
  split_ifs <;> rfl

@[simp] lemma Env.substNames_merge {Γ Δ : Env} {x y : FPName} :
  (Γ ++ Δ){y // x} =  Γ{y // x} ++ Δ{y // x} := by
  simp [HasSubst.subst, Env.substNames]

@[simp] lemma Env.substNames_nil {x y : FPName} :
  ([] : Env){x // y} = [] := by simp [HasSubst.subst, Env.substNames]

@[simp] lemma Env.substNames_empty {x y : FPName} : (∅ : Env){x // y} = ∅ := by
  simp

@[simp] lemma Env.substNames_self {Γ : Env} {x : FPName} :
  Γ{x // x} = Γ := by
  induction Γ generalizing x <;> simp_all [HasSubst.subst, Env.substNames]
  case cons hd tl ih =>
    intro h
    obtain ⟨hd1, hd2⟩ := hd
    simp_all

@[simp] lemma Env.mem_names_impl_mem_substNames {Γ : Env} {x y : FPName} :
  x ∈ Γ.names → y ∈ Γ{y // x}.names := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.mem_names_impl_mem_substNames' {Γ : Env} {x y : FPName}
  {hF : ∀ A, (y, A) ∉ Γ} :
  y ∈ Γ{y // x}.names → x ∈ Γ.names := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind

@[simp] lemma Env.mem_names_substNames_iff {Γ : Env} {x y z : FPName} :
  z ∈ Γ{y // x}.names ↔ (z = y ∧ x ∈ Γ.names) ∨ (z ∈ Γ.names ∧ z ≠ x) := by
  simp_all [HasSubst.subst, Env.substNames, Env.names]
  grind

@[simp] lemma Env.mem_substNames {Γ : Env} {x y : FPName} {A : Types} :
  (x, A) ∈ Γ → (y, A) ∈ Γ{y // x} := by
  simp_all [HasSubst.subst, Env.substNames]
  grind [Env.mem_pair_fst_in_names_iff]

@[simp] lemma Env.mem_substNames_of_ne {Γ : Env} {x y z : FPName} {A : Types} :
  (z, A) ∈ Γ → z ≠ x → (z, A) ∈ Γ{y // x} := by
  intro hin hneq
  simp [HasSubst.subst, Env.substNames]
  use z
  constructor
  · split_ifs with h
    · constructor
      · apply hin
      · simp_all
    · constructor
      · apply hin
      · rfl

lemma Env.fresh_substNames_aux {Γ : Env} {x y z : FPName}
  (hyz : y = z → y = x) (hyΓ : y ∈ Γ.names → y = x) (hF : z ∉ Γ.names) :
  (z{y // x}) ∉ (Γ{y // x}).names := by
  intro hc
  simp only [HasSubst.subst, substNames, beq_iff_eq, Prod.mk.eta, FPName.subst,
    mem_pair_fst_in_names_iff, List.mem_map, Prod.exists] at hc
  obtain ⟨A, a, B, ha, h⟩ := hc
  split_ifs at h with h1 h2 h3
  all_goals simp only [Prod.mk.injEq, true_and] at h
  case pos => subst h1 h2 ; exact hF (Env.mem_pair_fst_in_names _ ha)
  case neg => subst h1 ; rw [h.1] at hyz ; exact h2 (hyz (by rfl))
  case pos =>
    subst h3 ; rw [h.1] at ha h1
    exact h1 (hyΓ (Env.mem_pair_fst_in_names _ ha))
  case neg => rw [h.1] at ha ; exact hF (Env.mem_pair_fst_in_names _ ha)

lemma Env.fresh_substNames {Γ : Env} {x y z : FPName} {A : Types} (hF : z ∉ Γ.names)
  (huniq : ∀ Δ ∈ [z ∶ A :: Γ], ∀ (B : Types), (y, B) ∈ Δ → y = x) :
  z{y // x} ∉ Env.names Γ{y // x} := by
  apply Env.fresh_substNames_aux
  · intro hyz
    exact huniq (z ∶ A :: Γ) (by simp) A (by simp [hyz])
  · intro hyΓ
    obtain ⟨B, hB⟩ := Env.mem_pair_fst_in_names_iff.mp hyΓ
    exact huniq (z ∶ A :: Γ) (by simp) B (by simp [hB])
  · exact hF

@[simp] lemma Env.substNames_of_not_mem {Γ : Env} {x y : FPName} :
  x ∉ Γ.names → Γ{y // x} = Γ := by
  intro hF
  induction Γ
  case nil => simp
  case cons E Γ ih =>
    cases E
    case mk z A =>
      have : x ≠ z := by
        simp only [names_distributes, Finset.singleton_union, Finset.mem_insert,
          not_or, ← ne_eq] at hF
        exact hF.1
      simp only [substNames_distributes, List.cons.injEq, Prod.mk.injEq, and_true]
      constructor
      · simp [HasSubst.subst, FPName.subst]
        intro hc ; exfalso ; apply this hc.symm
      · exact ih (hF := by simp_all)

lemma Env.substNames_preserves_Types {Γ : Env} {x y : FPName} :
  ∀ z A, (z, A) ∈ Γ → (z{y // x}, A) ∈ Γ{y // x} := by
  simp [HasSubst.subst, Env.substNames, FPName.subst]
  intro z A hMem
  use z, A
  simp_all
  split_ifs <;> rfl

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

lemma Env.substNames_preserves_perm {Γ Δ : Env} {x y : FPName} :
  Γ ~ Δ → Γ{y // x} ~ Δ{y // x} := by
  simp_all [HasPerm.perm, HasSubst.subst, Env.substNames]
  grind

@[simp] lemma Env.serverUsable_shiftTypes {d c : Nat} {Γ : Env} :
  ?ₑΓ → ?ₑ(Γ ↑ d, c) := by
  simp [Env.serverUsable, HasShift.shift, Env.shiftTypes]
  intro h x A x' A' hMem heq hShift
  have := h x' A' hMem
  apply Types.isServerUsable_shift (d := d) (c := c).mp at this
  simp [HasShift.shift] at this
  rw [hShift] at this
  exact this

@[simp] lemma Env.shiftTypes_empty {d c : Nat} :
  ([] : Env) ↑ d, c = ([] : Env) := by
  simp [HasShift.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_singleton {d c : Nat} {x : FPName} {A : Types} :
  [x ∶ A] ↑ d, c = [x ∶ A ↑ d, c] := by
    simp [HasShift.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_cons {d k : Nat} {Γ : Env} {x : FPName} {A : Types} :
  (x ∶ A :: Γ) ↑ d, k = x ∶ A ↑ d, k :: Γ ↑ d, k := by
    simp [HasShift.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_append {d k : Nat} {Γ Δ : Env} :
  (Γ ++ Δ) ↑ d, k = Γ ↑ d, k ++ Δ ↑ d, k := by
    simp [HasShift.shift, Env.shiftTypes]

@[simp] lemma Env.shiftTypes_preserves_names {d c : Nat} {Γ : Env} :
  (Γ ↑ d, c).names = Γ.names := by
  simp [HasShift.shift, Env.shiftTypes, Env.names]
  rfl

@[simp] lemma Env.shiftTypes_preserves_disjoint {d c : Nat} {Γ Δ : Env} :
  Γ.disjoint Δ → (Γ ↑ d, c).disjoint (Δ ↑ d, c) := by simp

@[simp] lemma Env.shiftTypes_preserves_perm {d c : Nat} {Γ Δ : Env} :
  (Γ ~ Δ) → (Γ ↑ d, c ~ Δ ↑ d, c) := by
  simp [HasShift.shift]
  apply List.Perm.map

lemma Env.shiftTypes_comm {Γ : Env} {d c : Nat} :
  (Γ.shiftTypes d c).shiftTypes 0 1 = (Γ.shiftTypes 0 1).shiftTypes (d + 1) c := by
  induction Γ <;> grind [Env.shiftTypes, Types.shift_comm_0]

lemma Env.mem_serverUsable_Types {Γ : Env} {x : FPName} {A : Types} :
  ?ₑΓ → (x, A) ∈ Γ → A.isServerUsable := by
  intro hServ hMem
  simp [Env.serverUsable] at hServ
  exact hServ x A hMem

lemma Env.serverUsable_cons_mp {Γ : Env} {x : FPName} {A : Types} :
  A.isServerUsable ∧ ?ₑΓ → ?ₑ(x ∶ A :: Γ) := by
  simp [Env.serverUsable, Types.isServerUsable]

lemma Env.serverUsable_cons_mpr {Γ : Env} {x : FPName} {A : Types} :
  ?ₑ(x ∶ A :: Γ) → A.isServerUsable ∧ ?ₑΓ := by
  simp [Env.serverUsable, Types.isServerUsable]

lemma Env.serverUsable_cons_iff {Γ : Env} {x : FPName} {A : Types} :
  A.isServerUsable ∧ ?ₑΓ ↔ ?ₑ(x ∶ A :: Γ) := by
  constructor
  · exact Env.serverUsable_cons_mp
  · exact Env.serverUsable_cons_mpr

lemma Env.serverUsable_substNames {Γ : Env} {x y : FPName} :
  ?ₑΓ → ?ₑΓ{y // x} := by
  intro hServ
  simp [HasSubst.subst, Env.substNames, Env.serverUsable]
  intros z A w B hMem
  split_ifs <;> intro h <;> (
    simp_all
    exact Env.mem_serverUsable_Types hServ hMem
  )

@[simp] lemma Env.shiftTypes_substNames_comm {Γ : Env} {x y : FPName} :
  (Γ{y // x})⁺ = (Γ⁺){y // x} := by
  simp_all [HasSubst.subst, Env.substNames, HasShift.shift, Env.shiftTypes]
  intros ; split_ifs <;> rfl

lemma Env.mem_shiftTypes_iff {Γ : Env} {y : FPName} {T : Types} :
  (y, T) ∈ Γ⁺ ↔ ∃ A, (y, A) ∈ Γ ∧ T = A⁺ := by
  induction Γ
  case nil => simp
  case cons hd tl ih =>
    match hd with
    | (x, B) => simp_all ; grind

macro "fresh_substNames_binary_aux"
  z:term ", " C:term ", " Γ:term ", " Δ:term ", " huniq:term: tactic =>
  `(tactic| (
    intro Ξ hin T hMem
    simp at hin; subst hin
    simp at hMem
    rcases hMem with ⟨hyz, rfl⟩ | hin
    · exact $huniq:term ($z ∶ $C :: $Γ ++ $Δ) (by simp) $C (by simp [hyz])
    · apply $huniq:term ($z ∶ $C :: $Γ ++ $Δ) (by simp) T
      simp
      right ; left ; exact hin
      simp
  ))

lemma Env.fresh_substNames_binary {Γ Δ : Env} {x y z : FPName} {C : Types}
  (hF : z ∉ Γ.names ∧ z ∉ Δ.names)
  (huniq : ∀ Γ_1 ∈ [z ∶ C :: Γ ++ Δ], ∀ (T : Types), (y, T) ∈ Γ_1 → y = x) :
  z{y // x} ∉ Γ{y // x}.names ∧ z{y // x} ∉ Δ{y // x}.names := by
  cases hF
  case intro hFΓ hFΔ =>
  constructor
  · exact Env.fresh_substNames hFΓ (A := C) (by simp_all ; grind)
  · exact Env.fresh_substNames hFΔ (A := C) (by simp_all ; grind)

@[simp] lemma Env.serverUsable_substTypes {Γ : Env} {A : Types} {k : Nat} (h : ?ₑΓ) :
  (Γ.substTypes A k).serverUsable := by
  induction Γ
  case nil => intro p hp ; contradiction
  case cons hd tl ih =>
    match hd with
    | (x, T) =>
      intro p hp
      have hxT := by apply h (x, T) ; simp
      have htl : ?ₑtl := by intro q hq ; apply h q ; simp [hq]
      simp [Env.substTypes] at hp
      cases hp with
      | inl hphd =>
        rw [hphd] ; simp
        apply Types.isServerUsable_subst hxT
      | inr hptl =>
        apply ih htl
        simp [Env.substTypes]
        exact hptl

@[simp] lemma Env.substTypes_singleton {x : FPName} {A : Types} {k : Nat} :
  ([x ∶ A] : Env){A // k} = [x ∶ A{A // k}] := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_distributes {Γ : Env} {x : FPName} {A B : Types} {k : Nat} :
  (x ∶ B :: Γ){A // k} = x ∶ B{A // k} :: Γ{A // k} := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_merge {Γ Δ : Env} {A : Types} {k : Nat} :
  (Γ ++ Δ){A // k} =  Γ{A // k} ++ Δ{A // k} := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_nil {A : Types} {k : Nat} :
  ([] : Env){A // k} = [] := by simp [HasSubst.subst, Env.substTypes]

@[simp] lemma Env.substTypes_preserves_names {Γ : Env} {A : Types} {k : Nat} :
  Γ{A // k}.names = Γ.names := by
  simp [HasSubst.subst, Env.substTypes, Env.names]
  rfl

@[simp] lemma Env.substTypes_preserves_disjoint {Γ Δ : Env} {A : Types} {k : Nat} :
  Γ.disjoint Δ → Γ{A // k}.disjoint Δ{A // k} := by
  simp [Env.disjoint]

@[simp] lemma Env.substTypes_preserves_perm {Γ Δ : Env} {A : Types} {k : Nat} :
  (Γ ~ Δ) → (Γ{A // k} ~ Δ{A // k}) := by
  simp [HasPerm.perm, HasSubst.subst]
  apply List.Perm.map

-- Γ{A // k}⁺ = Γ⁺{A⁺ // k + 1}
@[simp] lemma Env.shiftTypes_substTypes_comm {Γ : Env} {A : Types} {k : Nat} :
  (Γ.substTypes A k).shiftTypes 0 1 = (Γ.shiftTypes 0 1).substTypes (A.shift 0 1) (k + 1) := by
  induction Γ <;> simp [Env.substTypes, Env.shiftTypes, Types.shift_0_subst_comm]

@[simp] lemma Env.shiftTypes_substTypes_cancel {Γ : Env} {A : Types} :
  Γ⁺{A // 0} = Γ := by
  induction Γ
  case nil => simp
  case cons E Γ ih =>
    cases E with
    | mk x T =>
      simp
      exact ih

@[simp] lemma Env.Nodup_nil :
  Env.Nodup [] := by simp [Nodup]

@[simp] lemma Env.Nodup_singleton {x : FPName} {A : Types} :
  Env.Nodup [x ∶ A] := by simp [Env.Nodup]
lemma Env.Nodup_perm {Γ Δ : Env} (hP : Γ ~ Δ) :
  Env.Nodup Γ → Env.Nodup Δ := by
  intro h
  have hPNames := List.Perm.map Prod.fst hP
  exact (List.Perm.nodup_iff hPNames).mp h

lemma Env.Nodup_cons {x : FPName} {A : Types} {Γ : Env} :
  Env.Nodup ((x, A) :: Γ) ↔ x ∉ Γ.names ∧ Env.Nodup Γ := by
  simp [Env.Nodup, Env.names]

lemma Env.Perm.nodup_iff {Γ Δ : Env} (h : Γ ~ Δ) :
  Env.Nodup Γ ↔ Env.Nodup Δ := by
  unfold Env.Nodup
  have hPNames := List.Perm.map Prod.fst h
  exact List.Perm.nodup_iff hPNames

@[simp] lemma Env.map_fst_shiftTypes {Γ : Env} :
  List.map Prod.fst Γ⁺ = List.map Prod.fst Γ := by
    simp [HasShift.shift, Env.shiftTypes]

@[simp] lemma Env.Nodup_shiftTypes {Γ : Env} :
  Env.Nodup Γ⁺ ↔ Env.Nodup Γ := by
  unfold Env.Nodup
  rw [Env.map_fst_shiftTypes]

lemma Env.names_empty_nil {Γ : Env} (h : Γ.names = ∅) :
  Γ = [] := by
  induction Γ
  case nil => simp
  case cons E htl ih => cases E ; simp [Env.names_distributes] at h

lemma Env.extract_exp {Γ : Env} {z : FPName}
  (hz : z ∈ Γ.names) (hServ : ?ₑΓ) (hNodup : Env.Nodup Γ) :
  ∃ A Γ', (Γ ~ z ∶ ??A :: Γ') ∧ (?ₑΓ') ∧ (Env.names Γ' = Γ.names \ {z}) := by
  induction Γ
  case nil => contradiction
  case cons E Γ ih =>
    obtain ⟨x, A⟩ := E
    simp [- mem_pair_fst_in_names_iff] at hz
    have hServΓ : ?ₑΓ := by
      intro p hp
      exact hServ p (List.Mem.tail _ hp)
    have hServA : A.isServerUsable := by
      exact hServ (x, A) (List.Mem.head _)
    cases A <;> try contradiction
    case quest A =>
      rcases hz with (rfl | hzΓ)
      · use A, Γ
        refine ⟨List.Perm.refl _, hServΓ, ?_⟩
        simp ; rw [← Finset.erase_eq, Finset.erase_insert]
        have this := (List.nodup_cons.mp hNodup).1
        simp_all [Env.mem_pair_fst_in_names_iff]
      · obtain ⟨B, Γ', hP', hServ', hNames'⟩ := ih hzΓ hServΓ ((Env.Nodup_cons.mp hNodup).2)
        use B, (x, ??A) :: Γ'
        constructor
        · apply List.Perm.trans (List.Perm.cons _ hP')
          apply List.Perm.swap
        · constructor
          · rw [Env.serverUsable]
            intro p hp
            simp at hp
            cases hp
            case inl h => subst h ; simp ; exact hServA
            case inr h =>
              cases p
              case mk x T =>
                exact Env.mem_serverUsable_Types hServ' h
          · simp [Env.names_distributes]
            rw [hNames']
            simp_all
            have h1 : x ∉ names Γ := by
              have := (List.nodup_cons.mp hNodup).1
              simp at this
              exact Env.not_mem_names_iff.mpr this
            have hneq : z ≠ x := by
              intro rfl
              exact h1 (by simp [hzΓ])
            ext a
            simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
            grind

@[simp] lemma Env.serverUsable_nil :
  ?ₑ[] := by simp [Env.serverUsable]

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

lemma Env.disjoint_of_perm {Γ Δ Γ' Δ' : Env} (hP1 : Γ ~ Γ') (hP2 : Δ ~ Δ')
  (hDisj : Env.disjoint Γ Δ) : Env.disjoint Γ' Δ' := by
  simp only [Env.disjoint] at *
  have h_names1 : Γ.names = Γ'.names := by
    ext x ; simp [Env.names]
    constructor
    · intro h
      obtain ⟨A, hinΓ⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP1).mp hinΓ
    · intro h
      obtain ⟨A, hinΓ'⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP1.symm).mp hinΓ'
  have h_names2 : Δ.names = Δ'.names := by
    ext x ; simp [Env.names]
    constructor
    · intro h
      obtain ⟨A, hinΔ⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP2).mp hinΔ
    · intro h
      obtain ⟨A, hinΔ'⟩ := h
      use A
      exact (List.Perm.mem_iff (a := (x, A)) hP2.symm).mp hinΔ'
  rw [← h_names1, ← h_names2]
  exact hDisj

@[simp] lemma Env.names_substNames_image_free {Γ : Env} {y x : FPName} :
  (Γ.names.image Channel.free){y // x} = (Γ{y // x}).names.image Channel.free := by
  ext u
  simp only [HasSubst.subst, Finset.subst, Finset.image_image, Env.names, Env.substNames,
    Finset.mem_image, List.mem_toFinset, List.mem_map, Prod.exists, beq_iff_eq]
  constructor
  · rintro ⟨c, ⟨z, B, hin, rfl⟩, rfl⟩
    simp only [↓existsAndEq, and_true, Channel.subst, beq_iff_eq,
      Function.comp_apply, exists_and_right]
    split_ifs with heq
    · subst heq
      use y
      constructor
      · use B, z, B, hin
        simp only [if_true]
      · rfl
    · use z
      constructor
      · use B, z, B, hin
        simp only [heq, if_false]
      · rfl
  · rintro ⟨_, ⟨w, B, ⟨z, B', hin, heq⟩, rfl⟩, rfl⟩
    split_ifs at heq with heq'
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      use z
      constructor
      · use z, B', hin
      · simp only [Channel.subst, beq_iff_eq, heq', Function.comp_apply, ↓reduceIte]
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      use z
      constructor
      · use z, B', hin
      · simp [Channel.subst, heq']
