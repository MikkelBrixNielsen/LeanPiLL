import PiLL.Framework.Semantics.EnvStep
import PiLL.Framework.Semantics.ProcStep
import PiLL.Framework.Substitution

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


-- FIXME: Fix TypingStep
-- FIXME: Typing_preserves_proc_congr
-- FIXME: Use NameSpaces instead of having e.g. HyperEnv._____ everywhere




-- FIXME: Proof showing substitution avoids capture
-- FIXME: Proof showing AlphaEq is equivalent to = between Procs
-- FIXME: Find different syntax for open?
-- FIXME: Prove name substitution only being applied to free names?


-- NOTE: shows the proof lean found using the simp_all tactic show_term { simp_all }

-- FIXME: Move everything related to HyperEnv.Perm to a separate file? Or at least organize
-- definition and lemma ordering a bit.

-- TODO: Change lemma naminig and dot notation interactions to follow standard pattern
-- TODO: Change HyperEnv.Nodup def to match Env
-- TODO: Change the names of the HyperEnv rotate left / right lemmas to match what they do





lemma ProcStep_buildDup_aux {n : Nat} {QL QR : Proc} {x : FPName} {A : Types}
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

lemma ProcStep_buildDup {n : Nat} {P : Proc} {x : FPName} {A : Types} {Γ : Env}
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

  apply ProcStep_buildDup_aux names Γ [] Γ
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
    rw [HyperEnv.Nodup_singleton, Env.Nodup_cons] at this
    exact this.1
  · simp
  · exact hlin.1
  · exact hlcΓx.2
  · simp
  · exact hlcΓx.2
  · exact hnd_names
  · use Γ ; simp [HasPerm.perm, heq_names]

lemma ProcStep_buildDisp {n : Nat} {x : FPName} (Γ : Env) (names : List FPName)
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

  case res 𝒢 ℋ Γ Γ' Δ Δ' u v A  l hFu hFv hFu' hFv' hFlu hFlv hneq hES ih =>
    simp [Env.Nodup_merge_iff] at hnd
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at hFu hFv hFu' hFv'

    have hndΓu: HyperEnv.Nodup [u ∶ Aᗮ :: Γ] := by
      simp [Env.Nodup_cons, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff]
      exact ⟨hFu.2.1, hnd.2.1⟩

    have hndΔv : HyperEnv.Nodup [v ∶ A :: Δ] := by
      simp [Env.Nodup_cons, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff]
      exact ⟨hFv.2.2, hnd.2.2.1⟩

    have hnd' := And.intro (And.intro hnd.1 hndΓu) hndΔv

    simp only [HyperEnv.Nodup_merge] at ih
    obtain ⟨𝒢ᵣ_ih, Γ_ih, h_pre_ih, h_post_ih⟩ := ih hnd' hl

    rw [← hl] at hFlu hFlv
    simp [← ne_eq] at hFlu hFlv
    symm at hFlu hFlv

    exact HyperEnv.Perm.extract_bot_res
      h_pre_ih h_post_ih hFlu hFlv hFu.1 hFv.1 hFu'.1 hFv'.1 hneq hFu.2.2 hFv.2.1

  case perm 𝒢 𝒢' ℋ ℋ' _ hP _ hP' ih =>
    have := HyperEnv.Nodup_perm hP.symm hnd
    obtain ⟨𝒥, Γ, h_pre_ih, h_post_ih⟩ := ih this hl
    use 𝒥, Γ
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP) h_pre_ih
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP') h_post_ih

lemma HyperEnv.Perm.extract_one_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [[z ∶ 1]])
  (h_post : ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] ~ 𝒢ᵣ)
  (hzx : z ≠ x) (hzy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hneq : x ≠ y) (hxΔ : x ∉ Δ.names) (hyΓ : y ∉ Γ.names) :
  ∃ 𝒢ᵣ',
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ' |ₕ [[z ∶ 1]] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ' := by

  have hzin : ([z ∶ 1]) ∈ 𝒢ᵣ |ₕ [[z ∶ 1]] := by simp

  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hzin

  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ : ∃ 𝒢ᵣ, 𝒢 ~ E :: 𝒢ᵣ :=
        HyperEnv.exists_perm_cons_of_mem h

      have h𝒢' : 𝒢 ~ [z ∶ 1] :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)
      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], ?_, ?_⟩
      · have := h𝒢_split.symm.trans h𝒢'
        apply HyperEnv.Perm_rotate_rhs_right
        apply HyperEnv.Perm.merge
        · rw [HyperEnv.cons_append] at h𝒢'
          exact h𝒢'
        · rfl
      · have h𝒢ᵣ : 𝒢ᵣ ~ 𝒢ᵣ' |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] := by
          have h_pre_subst : ([z ∶ 1] :: 𝒢ᵣ') |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~
            𝒢ᵣ |ₕ [[z ∶ 1]] := by
            simp [HasPerm.perm] at hPE
            subst hPE
            apply HyperEnv.Perm.merge_right (𝒥 := [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]) at h𝒢_split
            simp only [← HyperEnv.merge_assoc] at h𝒢_split
            exact h𝒢_split.symm.trans h_pre
          rw [HyperEnv.cons_append, HyperEnv.merge_assoc] at h_pre_subst
          symm at h_pre_subst
          apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
          apply HyperEnv.Perm_merge_cancel_right at h_pre_subst
          rw [HyperEnv.merge_assoc]
          exact h_pre_subst

        have h_post_subst : ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] ~
          𝒢ᵣ' |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] :=
          h_post.trans h𝒢ᵣ

        have hPΓΓ' : x ∶ Aᗮ :: Γ' ~ x ∶ Aᗮ :: Γ := by
          have hxin : (x ∶ Aᗮ :: Γ') ∈ ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEx : (x, Aᗮ) ∈ E := by
                have := hPE.symm.subset
                simp at this
                obtain ⟨h1, h2⟩ := this
                exact h1

              have hx𝒢: x ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEx))

              apply hFx hx𝒢

            case inr h =>
              subst h
              apply List.Perm.symm
              exact hPE

          · exfalso
            have hxiny : (x, Aᗮ) ∈ y ∶ A :: Δ := by
              have := hPE.symm.subset
              simp at this ⊢
              exact this.1

            simp at hxiny
            rcases hxiny with heq | hΔ
            · rw [heq.1] at hneq
              contradiction
            · exact hxΔ (Env.mem_pair_fst_in_names _ hΔ)

        have hPΔΔ' : y ∶ A :: Δ' ~ y ∶ A :: Δ := by
          have hxin : (y ∶ A :: Δ') ∈ ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] := by simp
          obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_post_subst.symm hxin
          simp only [List.mem_append, List.mem_singleton] at hE
          rcases hE with h | rfl | rfl
          · cases h
            case inl h =>
              exfalso
              have hEy : (y, A) ∈ E := by
                have := hPE.symm.subset
                simp at this
                obtain ⟨h1, h2⟩ := this
                exact h1

              have hy𝒢: y ∈ 𝒢.names := by
                have heq_names := HyperEnv.names_eq_of_perm h𝒢'
                rw [heq_names]
                simp only [HyperEnv.names_cons, Finset.mem_union]
                exact Or.inr (HyperEnv.subset_names_of_mem h (Env.mem_pair_fst_in_names _ hEy))

              apply hFy hy𝒢

            case inr h =>
              exfalso
              subst h
              have hyinx : (y, A) ∈ x ∶ Aᗮ :: Γ := by
                have := hPE.symm.subset
                simp at this ⊢
                exact this.1
              simp at hyinx
              cases hyinx
              case inl h =>
                rw [h.1] at hneq
                contradiction
              case inr h =>
                exact hyΓ (Env.mem_pair_fst_in_names _ h)

          · simp [HasPerm.perm] at hPE ⊢
            exact hPE.symm

        have hPℋ𝒢 : ℋ ~ 𝒢ᵣ' := by
          have hP1 : 𝒢ᵣ' |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~
            𝒢ᵣ' |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] := by
            apply HyperEnv.Perm.merge
            · apply HyperEnv.Perm.merge
              · rfl
              · exact HyperEnv.Perm.cons hPΓΓ'.symm rfl
            · exact HyperEnv.Perm.cons hPΔΔ'.symm rfl

          apply HyperEnv.Perm_merge_cancel_right (𝒥 := [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'])
          simp only [← HyperEnv.merge_assoc]
          exact h_post_subst.trans hP1

        apply HyperEnv.Perm.merge
        · exact hPℋ𝒢
        · apply HyperEnv.Perm.cons
          · apply List.Perm.append
            · exact List.Perm.cons_inv (a := x ∶ Aᗮ) hPΓΓ'
            · exact List.Perm.cons_inv (a := y ∶ A) hPΔΔ'
          · rfl

    case inr h =>
      rw [h] at hPE
      simp [HasPerm.perm] at hPE
      rw [hPE.1.1] at hzx
      contradiction

  · exfalso
    simp [HasPerm.perm] at hPE
    rw [hPE.1.1] at hzy
    contradiction

lemma EnvStep_inv_one {𝒢 𝒢' : HyperEnv} {x : FPName}
  (hnd : 𝒢.Nodup) (hES : 𝒢 -[x⟦⟧]->ₑ 𝒢') :
  ∃ 𝒢_rest, (𝒢 ~ 𝒢_rest |ₕ [[x ∶ 1]]) ∧ (𝒢' ~ 𝒢_rest) := by
  generalize hl : (x⟦⟧ : Lbl) = l at hES
  induction hES <;> try contradiction
  all_goals simp at hl

  case one =>
    use ∅
    subst hl
    simp

  case par₁ 𝒥 _ _ _ ih =>
    simp at hnd
    obtain ⟨𝒢ᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hnd.1 hl
    use (𝒢ᵣ_ih |ₕ 𝒥)
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm.merge
      · apply HyperEnv.Perm_exchange_rhs
        · exact HyperEnv.Perm.merge_comm
        · exact h_pre_ih
      · rfl
    · exact HyperEnv.Perm.merge h_post_ih (by rfl)

  case par₂ 𝒥 _ _ _ _ _ ih =>
    simp at hnd
    obtain ⟨ℋᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hnd.2 hl
    use (𝒥 |ₕ ℋᵣ_ih)
    constructor
    · rw [HyperEnv.merge_assoc]
      exact HyperEnv.Perm.merge (by rfl) h_pre_ih
    · exact HyperEnv.Perm.merge (by rfl) h_post_ih

  case res 𝒢 ℋ Γ Γ' Δ Δ' u v A l hFu hFv hFu' hFv' hFlu hFlv hneq hES ih =>
    simp [Env.Nodup_merge_iff] at hnd
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at hFu hFv hFu' hFv'

    have hndΓu: HyperEnv.Nodup [u ∶ Aᗮ :: Γ] := by
      simp [Env.Nodup_cons, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff]
      exact ⟨hFu.2.1, hnd.2.1⟩

    have hndΔv : HyperEnv.Nodup [v ∶ A :: Δ] := by
      simp [Env.Nodup_cons, - Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff]
      exact ⟨hFv.2.2, hnd.2.2.1⟩

    have hnd' := And.intro (And.intro hnd.1 hndΓu) hndΔv

    simp only [HyperEnv.Nodup_merge] at ih
    obtain ⟨𝒢ᵣ_ih, h_pre_ih, h_post_ih⟩ := ih hnd' hl

    rw [← hl] at hFlu hFlv
    simp [← ne_eq] at hFlu hFlv
    symm at hFlu hFlv

    exact HyperEnv.Perm.extract_one_res
      h_pre_ih h_post_ih hFlu hFlv hFu.1 hFv.1 hneq hFu.2.2 hFv.2.1

  case perm hP _ hP' ih =>
    obtain ⟨𝒥, h_pre_ih, h_post_ih⟩ := ih (HyperEnv.Nodup_perm hP.symm hnd) hl
    use 𝒥
    constructor
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP) h_pre_ih
    · exact HyperEnv.Perm.trans (HyperEnv.Perm.symm hP') h_post_ih

lemma HyperEnv.Perm.extract_one_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {u v x y : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [u ∶ Aᗮ :: Γ'] |ₕ [v ∶ A :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (h_xu : x ≠ u) (h_xv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
  (hFu : u ∉ 𝒢.names) (hFv : v ∉ 𝒢.names)
  (hFu' : u ∉ ℋ.names) (hFv' : v ∉ ℋ.names)
  (hneq : u ≠ v) (hvΓ : v ∉ Γ.names) (huΔ : u ∉ Δ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by

  have hxin : ([x ∶ 1]) ∈ 𝒢ᵣ |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre hxin

  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · cases h
    case inl h =>
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ := HyperEnv.exists_perm_cons_of_mem h
      have h𝒢' := h𝒢_split.trans (HyperEnv.Perm.cons hPE (.refl _))

      have h_pre_bot : 𝒢ᵣ' |ₕ [u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ] := by
        have := HyperEnv.Perm.merge_right h𝒢' ([u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ])
        rw [← HyperEnv.merge_assoc] at this
        have := this.symm.trans h_pre
        apply HyperEnv.Perm_rotate_rhs_right at this
        rw [HyperEnv.merge_assoc, ← HyperEnv.cons_append, ← HyperEnv.cons_append] at this
        apply HyperEnv.Perm.cons_cancel_left at this
        rw [← HyperEnv.merge_nilR (𝒢ᵣ |ₕ [y ∶ ⊥ :: Ξ])]
        apply HyperEnv.Perm_rotate_rhs_left
        simp at ⊢ this
        exact this

      simp [HasPerm.perm] at hPE
      subst hPE

      have hFuᵣ : u ∉ HyperEnv.names 𝒢ᵣ':= by
        intro hc
        exact hFu (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])

      have hFvᵣ : v ∉ HyperEnv.names 𝒢ᵣ' := by
        intro hc
        exact hFv (by simp [hc, (HyperEnv.names_eq_of_perm h𝒢_split)])

      obtain ⟨𝒢ᵣ'', Γₙ, h_pre', h_post'⟩ :=
        HyperEnv.Perm.extract_bot_res h_pre_bot h_post hyu hyv hFuᵣ hFvᵣ hFu' hFv' hneq huΔ hvΓ

      refine ⟨𝒢ᵣ'', Γₙ, ?_, h_post'⟩
      · have h1 := HyperEnv.Perm.merge_right h𝒢_split ([Γ‚ Δ])
        have h2 := HyperEnv.Perm.merge_right h_pre' ([[x ∶ 1]])
        conv_rhs at h1 => rw [HyperEnv.cons_append]
        apply HyperEnv.Perm_rotate_rhs_right at h1
        conv_rhs at h2 => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h2
        rw [← HyperEnv.merge_assoc] at h2
        apply HyperEnv.Perm_rotate_rhs_right at h2
        exact h1.trans h2

    case inr h =>
      subst h
      simp [HasPerm.perm] at hPE
      obtain ⟨⟨h1, _⟩, _⟩ := hPE
      subst h1
      contradiction

  · simp [HasPerm.perm] at hPE
    obtain ⟨⟨h1, _⟩, _⟩ := hPE
    subst h1
    contradiction

lemma EnvStep_inv_one_bot {𝒢 ℋ : HyperEnv} {x y : FPName}
  (hnd : 𝒢.Nodup) (hES : 𝒢 -[x⟦⟧ |ₗ y⸨⸩]->ₑ ℋ) :
  ∃ 𝒢' Γ,
    (𝒢 ~ 𝒢' |ₕ [[x ∶ 1]] |ₕ [y ∶ ⊥ :: Γ]) ∧
    (ℋ ~ 𝒢' |ₕ [Γ]) := by
  generalize hl : (x⟦⟧ |ₗ y⸨⸩) = lbl at hES
  induction hES <;> try contradiction
  all_goals simp at hl hnd

  case par₁ 𝒥 _ _ hFl ih =>
    obtain ⟨𝒢ᵣ, Γₙ, h_pre_ih, h_post_ih⟩ := ih hnd.1 hl
    refine ⟨𝒥 |ₕ 𝒢ᵣ, Γₙ, ?_, ?_⟩
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm.merge
      · rw [← HyperEnv.merge_assoc]
        exact h_pre_ih
      · rfl
    · apply HyperEnv.Perm_rotate_rhs_left
      apply HyperEnv.Perm.merge
      · exact h_post_ih
      · rfl

  case par₂ 𝒥 _ _ _ _ hFl ih =>
    obtain ⟨ℋᵣ, Γₙ, h_pre_ih, h_post_ih⟩ := ih hnd.2 hl
    refine ⟨𝒥 |ₕ ℋᵣ, Γₙ, ?_, ?_⟩
    · rw [HyperEnv.merge_assoc, HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge
      · rfl
      · rw [← HyperEnv.merge_assoc]
        exact h_pre_ih
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm.merge
      · rfl
      · exact h_post_ih

  case syn hES𝒢 hESℋ hFl lwf ih𝒢 ihℋ =>
    obtain ⟨hlx, hly⟩ := hl
    obtain ⟨𝒢_rest1, h_pre1, h_post1⟩ := EnvStep_inv_one hnd.1 (hlx ▸ hES𝒢)
    obtain ⟨𝒢_rest2, Γₙ, h_pre2, h_post2⟩ := EnvStep_inv_bot hnd.2 (hly ▸ hESℋ)
    refine ⟨𝒢_rest1 |ₕ 𝒢_rest2, Γₙ, ?_, ?_⟩
    · have := h_pre1.merge h_pre2
      apply HyperEnv.Perm_pull_rhs_mid_left at this
      rw [HyperEnv.merge_assoc] at this
      apply HyperEnv.Perm_pull_rhs_mid_left at this
      simp only [← HyperEnv.merge_assoc] at this
      exact this
    · rw [HyperEnv.merge_assoc]
      exact h_post1.merge h_post2

  case res 𝒥 𝒥' Γ Γ' Δ Δ' u v A l hFu hFv hFu' hFv' hFl hFl' hneq hES ih =>
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at hFu hFv hFu' hFv'
    have hnd_inner : (𝒥 |ₕ [u ∶ Aᗮ :: Γ] |ₕ [v ∶ A :: Δ]).Nodup := by
      simp
      obtain ⟨hnd1, hnd2⟩ := hnd
      simp [Env.Nodup_merge_iff] at hnd2
      constructor
      · exact hnd1
      · simp [HyperEnv.Nodup]
        constructor
        · exact Env.Nodup_cons.mpr ⟨hFu.2.1, hnd2.1⟩
        · exact Env.Nodup_cons.mpr ⟨hFv.2.2, hnd2.2.1⟩

    obtain ⟨𝒢ᵣ_inner, Ξ, h_pre_ih, h_post_ih⟩ := ih hnd_inner hl

    rw [← hl] at hFl hFl'
    simp [← ne_eq] at hFl hFl'

    obtain ⟨𝒢ᵣ_new, Γₙ, h_pre_final, h_post_final⟩ :=
      HyperEnv.Perm.extract_one_bot_res
        h_pre_ih h_post_ih
        hFl.2.symm
        hFl'.2.symm
        hFl.1.symm
        hFl'.1.symm
        hFu.1 hFv.1 hFu'.1 hFv'.1
        hneq hFv.2.1 hFu.2.2

    exact ⟨𝒢ᵣ_new, Γₙ, h_pre_final, h_post_final⟩

  case perm hP _ hP' ih =>
    obtain ⟨𝒢ᵣ, Γₙ, h_pre_ih, h_post_ih⟩:= ih (HyperEnv.Nodup_perm hP.symm hnd) hl
    use 𝒢ᵣ, Γₙ
    constructor
    · exact hP.symm.trans h_pre_ih
    · exact hP'.symm.trans h_post_ih





lemma HyperEnv.mem_of_mem_mem_names {𝒢 : HyperEnv} {Γ : Env} {x : FPName} {A : Types}
  (h₁ : x ∶ A ∈ Γ) (h₂ : Γ ∈ 𝒢) : x ∈ 𝒢.names := by
  induction 𝒢
  case nil => simp_all
  case cons E HE ih =>
    simp at h₂
    cases h₂
    case inl h =>
      subst h
      simp
      apply Or.inl
      use A
    case inr h =>
      simp
      apply Or.inr
      apply ih h

lemma HyperEnv.not_mem_names_iff {𝒢 : HyperEnv} {x : FPName} :
  x ∉ 𝒢.names ↔ ∀ (Γ : Env) (A : Types), Γ ∈ 𝒢 → (x, A) ∉ Γ := by
  induction 𝒢
  case nil => simp
  case cons E HE ih =>
    constructor
    · intro h1 Γ A hin
      simp [-Env.mem_pair_fst_in_names_iff, -Env.not_mem_names_iff] at h1 hin
      obtain ⟨hE, hHE⟩ := h1
      cases hin
      case inl h =>
        subst h
        exact Env.not_mem_names_iff.mp hE A
      case inr h =>
        exact ih.mp hHE Γ A h
    · intro h
      have h' := h E
      simp at h h' ⊢
      constructor
      · have := Env.not_mem_names_iff.mpr h'
        simp at this
        exact this
      · apply ih.mpr
        intro Γ A hin
        exact h Γ A (Or.inr hin)

lemma HyperEnv.PairwiseDisjoint_tail_not_in_head {𝒢 ℋ : HyperEnv} :
  List.Pairwise Env.disjoint (𝒢 |ₕ ℋ) →
  (∀ E, E ∈ ℋ → ∀ x A, (x ∶ A) ∈ E → x ∉ 𝒢.names) := by
  intros h Γ hΓinℋ x A hinΓ hxin𝒢
  have h_cross := (List.pairwise_append.mp h).2.2
  obtain ⟨B, Δ, hinΔ, hΔin𝒢⟩ := HyperEnv.mem_pair_fst_in_names.mp hxin𝒢
  have hxΓ : x ∈ Γ.names := Env.mem_pair_fst_in_names _ hinΓ
  have hxΔ : x ∈ Δ.names := Env.mem_pair_fst_in_names _ hinΔ
  have hD := h_cross Δ hΔin𝒢 Γ hΓinℋ
  exact Finset.disjoint_left.mp hD hxΔ hxΓ

lemma HyperEnv.fresh_of_linear_res
  {ℋ' ℋᵣ : HyperEnv} {Γ Δ : Env} {P : Proc} {x y : FPName} {A : Types} {n : Nat}
  (hT : n ⊢ P⸨#x, #y⸩ ∷ ℋ') (hP : ℋ' ~ ℋᵣ |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) :
  (x ∉ ℋᵣ.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names) ∧
  (y ∉ ℋᵣ.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names) := by

  have := Typing_preserves_linearity hT
  have hpwᵣ := (HyperEnv.Perm_PairwiseDisjoint_iff hP).mp this.2
  have hnd := (HyperEnv.Nodup_perm_iff hP).mp this.1

  rw [HyperEnv.merge_assoc] at hpwᵣ
  have hxninℋᵣ := HyperEnv.PairwiseDisjoint_tail_not_in_head hpwᵣ
    (x ∶ A :: Γ) (by simp) x A (by simp)

  simp [HyperEnv.Nodup_merge] at hnd
  simp [HyperEnv.Nodup, Env.Nodup_cons, - Env.mem_pair_fst_in_names_iff,
    - Env.not_mem_names_iff] at hnd

  apply HyperEnv.Perm_rotate_rhs_left at hP
  have hpwᵣ' := (HyperEnv.Perm_PairwiseDisjoint_iff hP).mp this.2
  rw [HyperEnv.merge_assoc] at hpwᵣ'

  have hxninΔ := by
    have := HyperEnv.PairwiseDisjoint_tail_not_in_head hpwᵣ'
      (x ∶ A :: Γ) (by simp) x A (by simp)
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at this
    exact this.2

  have hyninℋᵣ := HyperEnv.PairwiseDisjoint_tail_not_in_head hpwᵣ
    (y ∶ Aᗮ :: Δ) (by simp) y Aᗮ (by simp)

  apply HyperEnv.Perm_rotate_rhs_left at hP
  have hpwᵣ' := (HyperEnv.Perm_PairwiseDisjoint_iff hP).mp this.2
  rw [HyperEnv.merge_assoc] at hpwᵣ'
  have hyninΓ := by
    have := HyperEnv.PairwiseDisjoint_tail_not_in_head hpwᵣ'
      (y ∶ Aᗮ :: Δ) (by simp) y Aᗮ (by simp)
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff] at this
    exact this.2

  exact ⟨⟨hxninℋᵣ, hnd.2.1.1, hxninΔ⟩, ⟨hyninℋᵣ, hyninΓ, hnd.2.2.1⟩⟩

lemma Channel.open_rec_substNames {u : Channel} {x y z : FPName} {k : Nat} :
  (u⸨k | #z⸩){y // x} = u{y // x}⸨k | #(z{y // x})⸩ := by
  cases u <;>
    simp [HasOpen.open_, Channel.open, HasSubst.subst, Channel.subst, FPName.subst] <;>
    split_ifs <;> simp
  case pos h =>
    intro h'
    exfalso
    exact h' h
  case neg h =>
    intro h'
    exfalso
    exact h h'

lemma Proc.open_rec_substNames {P : Proc} {x y z : FPName} {k : Nat} :
  (P⸨k | #z⸩){y // x} = (P{y // x})⸨k | #(z{y // x})⸩ := by
  induction P generalizing k <;> simp [Channel.open_rec_substNames, *]

lemma Proc.open_substNames {P : Proc} {x y z : FPName} :
  P⸨#z⸩{y // x} = (P{y // x})⸨#(z{y // x})⸩ := by
  exact Proc.open_rec_substNames

lemma Proc.open_two_substNames {P : Proc} {x y z w : FPName} :
  (P⸨#z, #w⸩){y // x} = (P{y // x})⸨#(z{y // x}), #(w{y // x})⸩ := by
  change (P⸨1 | #w⸩⸨0 | #z⸩){y // x} = _
  rw [Proc.open_rec_substNames]
  rw [Proc.open_rec_substNames]
  rfl

lemma Proc.substNames_of_not_mem {P : Proc} {x y : FPName} (h : x ∉ P.f) :
  P{y // x} = P := by
  induction P <;> simp_all

  case one u P ih | bot u P ih | tensor u P ih | parr u P ih | selectL u P ih | selectR u P ih
    | output u P A ih | input u P ih | server u P ih | consume u P ih | duplicate u P ih
    | dispose u P ih | amp u P Q ihP ihQ =>
    cases u
    case free w =>
      simp_all [← ne_eq, Channel.f]
      rw [FPName.subst_self_of_ne h.1.symm]
    case bound i => simp

  case link u v =>
    constructor
    · cases u
      case free w =>
        simp_all [← ne_eq, Channel.f]
        rw [FPName.subst_self_of_ne h.1.symm]
      case bound i => simp
    · cases v
      case free w =>
        simp_all [← ne_eq, Channel.f]
        rw [FPName.subst_self_of_ne h.2.symm]
      case bound i => simp

lemma Typing_res_exists {n : Nat} {P : Proc} {𝒢 : HyperEnv} {Γ Δ : Env} {A : Types} {x y : FPName}
  (hx : x ∉ 𝒢.names ∧ x ∉ Γ.names ∧ x ∉ Δ.names ∧ x ∉ P.f)
  (hy : y ∉ 𝒢.names ∧ y ∉ Γ.names ∧ y ∉ Δ.names ∧ y ∉ P.f)
  (hneq : x ≠ y)
  (hT : n ⊢ P⸨#x, #y⸩ ∷ 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]) :
  n ⊢ 𝑣⸨$N,$N⸩ P ∷ 𝒢 |ₕ [Γ‚ Δ] := by

  apply Typing.cut (A := A) (𝒢.names ∪ Γ.names ∪ Δ.names ∪ {x, y})
  intros z w hz hw hzw
  simp [← ne_eq] at hz hw

  have hTz := Typing_substNames (x := x) (y := z) hT ?_
  · have hTzw := Typing_substNames (x := y) (y := w) hTz ?_
    · simp [Proc.open_two_substNames] at hTzw ⊢

      rw [Proc.substNames_of_not_mem, Proc.substNames_of_not_mem hx.2.2.2,
        HyperEnv.substNames_of_not_mem hx.1, HyperEnv.substNames_of_not_mem hy.1,
        Env.substNames_of_not_mem hx.2.1, Env.substNames_of_not_mem hy.2.1,
        Env.substNames_of_not_mem hx.2.2.1, Env.substNames_of_not_mem hy.2.2.1,
        FPName.subst_self_of_ne hz.2.1, FPName.subst_self_of_ne hneq.symm,
        FPName.subst_self] at hTzw
      · exact hTzw
      · rw [Proc.substNames_of_not_mem hx.2.2.2]
        exact hy.2.2.2

    · intros Ξ hΞ A hinΞ
      simp at hΞ
      cases hΞ
      case inl h =>
        exfalso
        rw [HyperEnv.substNames_of_not_mem hx.1] at h
        apply hw.2.2.1 (HyperEnv.mem_of_mem_mem_names hinΞ h)
      case inr h =>
        cases h
        case inl h =>
          rw [Env.substNames_of_not_mem hx.2.1] at h
          subst h
          simp at hinΞ
          cases hinΞ
          case inl h =>
            obtain ⟨rfl, _⟩ := h
            contradiction
          case inr h =>
            exfalso
            exact hw.2.2.2.1 A h
        case inr h =>
          subst h
          simp at hinΞ
          cases hinΞ
          case inl h =>
            rw [FPName.subst_self_of_ne hneq.symm] at h
            obtain ⟨rfl, h2⟩ := h
            rfl
          case inr h =>
            exfalso
            rw [Env.substNames_of_not_mem hx.2.2.1] at h
            exact hw.2.2.2.2 A h
  · intros Ξ hΞ A hinΞ
    simp at hΞ
    cases hΞ
    case inl h =>
      exfalso
      apply hz.2.2.1 (HyperEnv.mem_of_mem_mem_names hinΞ h)
    case inr h =>
      cases h
      case inl h =>
        subst h
        simp at hinΞ
        cases hinΞ
        case inl h =>
          obtain ⟨rfl, _⟩ := h
          rfl
        case inr h =>
          exfalso
          exact hz.2.2.2.1 A h
      case inr h =>
        subst h
        simp at hinΞ
        cases hinΞ
        case inl h =>
          obtain ⟨rfl, h2⟩ := h
          have := hz.2.1
          contradiction
        case inr h =>
          exfalso
          exact hz.2.2.2.2 A h

lemma HyperEnv.Perm_nil_inv {𝒢 : HyperEnv} :
  𝒢.Perm [] ↔ 𝒢 = [] := by
  constructor
  · intro h
    generalize h1 : [] = ℋ at h
    induction h <;> simp_all
  · intro h ; subst h ; simp

lemma HyperEnv.Perm_singleton_inv {Γ : Env} {ℋ : HyperEnv} (h : ([Γ] : HyperEnv) ~ ℋ) :
  ∃ Δ, ℋ = [Δ] ∧ Γ ~ Δ := by
  generalize heq : ([Γ] : HyperEnv) = G at h
  induction h generalizing Γ <;> try simp_all
  case cons E1 E2 H1 H2 hPE ih =>
    obtain ⟨h1, h2⟩ := heq
    subst h1 h2
    have := HyperEnv.Perm_nil_inv.mp ih.symm
    subst this
    rfl
  case trans hP1 hP2 ih1 ih2 =>
    obtain ⟨Δ, hΔ, hP1⟩ := ih1 heq
    obtain ⟨Ξ, hΞ, hP2⟩ := ih2 hΔ.symm
    exact ⟨Ξ, hΞ, hP1.trans hP2⟩

lemma HyperEnv.Perm_singleton_singleton {Γ Δ : Env} :
  ([Γ] : HyperEnv) ~ [Δ] ↔ Γ ~ Δ := by
  constructor
  · intro h
    obtain ⟨Δ', heq, hP⟩ := HyperEnv.Perm_singleton_inv h
    injection heq with hhd
    subst hhd
    exact hP
  · intro h ; exact HyperEnv.Perm.cons h HyperEnv.Perm.nil

lemma HyperEnv.Perm.extract_link_res
  {𝒥 𝒥' : HyperEnv} {Γ Γ' Δ Δ' : Env} {z w x y : FPName} {A B : Types}
  (hP : 𝒥 |ₕ [z ∶ Aᗮ :: Γ] |ₕ [w ∶ A :: Δ] ~ 𝒥' |ₕ [z ∶ Aᗮ :: Γ']
    |ₕ [w ∶ A :: Δ'] |ₕ [[x ∶ Bᗮ, y ∶ B]])
  (hFz' : z ∉ 𝒥'.names ∧ z ∉ Γ'.names ∧ z ∉ Δ'.names)
  (hFw' : w ∉ 𝒥'.names ∧ w ∉ Γ'.names ∧ w ∉ Δ'.names)
  (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) (hneq : z ≠ w) :
  Γ ~ Γ' ∧ Δ ~ Δ' ∧ 𝒥 ~ 𝒥' |ₕ [[x ∶ Bᗮ, y ∶ B]] := by

  have h1 : [z ∶ Aᗮ :: Γ] ~ [z ∶ Aᗮ :: Γ'] := by
    have ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem hP.symm (Γ := z ∶ Aᗮ :: Γ) (by simp)
    simp at hE
    cases hE
    case inl h =>
      exfalso
      have := (List.Perm.mem_iff (a := z ∶ Aᗮ) hPE).mpr (by simp)
      have := HyperEnv.mem_of_mem_mem_names this h
      exact hFz'.1 this
    case inr h =>
      cases h
      case inl h =>
        subst h
        rw [HyperEnv.Perm_singleton_singleton]
        exact hPE.symm
      case inr h =>
        cases h
        case inl h =>
          subst h
          exfalso
          have hzin := (List.Perm.mem_iff (a := z ∶ Aᗮ) hPE).mpr (by simp)
          simp at hzin
          cases hzin
          case inl h =>
            obtain ⟨h1, h2⟩ := h
            contradiction
          case inr h =>
            exact hFz'.2.2 (Env.mem_pair_fst_in_names _ h)
        case inr h =>
          subst h
          have hzin := (List.Perm.mem_iff (a := z ∶ Aᗮ) hPE).mpr (by simp)
          simp at hzin
          cases hzin <;> (
            rename_i h
            obtain ⟨h1, h2⟩ := h
            contradiction
          )

  have h2 : [w ∶ A :: Δ] ~ [w ∶ A :: Δ'] := by
    have ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem hP.symm (Γ := w ∶ A :: Δ) (by simp)
    simp at hE
    cases hE
    case inl h =>
      exfalso
      have := (List.Perm.mem_iff (a := w ∶ A) hPE).mpr (by simp)
      have := HyperEnv.mem_of_mem_mem_names this h
      exact hFw'.1 this
    case inr h =>
      cases h
      case inl h =>
        subst h
        exfalso
        have hzin := (List.Perm.mem_iff (a := w ∶ A) hPE).mpr (by simp)
        simp at hzin
        cases hzin
        case inl h =>
          rw [h.1] at hneq
          contradiction
        case inr h =>
          exact hFw'.2.1 (Env.mem_pair_fst_in_names _ h)
      case inr h =>
        cases h
        case inl h =>
          subst h
          rw [HyperEnv.Perm_singleton_singleton]
          exact hPE.symm
        case inr h =>
        subst h
        have hzin := (List.Perm.mem_iff (a := w ∶ A) hPE).mpr (by simp)
        simp at hzin
        cases hzin <;> (
          rename_i h
          obtain ⟨h1, h2⟩ := h
          contradiction
        )

  have h3 : 𝒥 ~ 𝒥' |ₕ [[x ∶ Bᗮ, y ∶ B]] := by
    have h4 := (hP.symm.trans (HyperEnv.Perm.merge (HyperEnv.Perm.merge rfl h1) h2)).symm

    apply HyperEnv.Perm_rotate_rhs_left at h4
    apply HyperEnv.Perm_merge_cancel_right at h4
    rw [← HyperEnv.merge_assoc] at h4
    apply HyperEnv.Perm_merge_cancel_right at h4

    apply HyperEnv.Perm.trans
    · exact h4
    · apply HyperEnv.Perm.merge_comm

  rw [HyperEnv.Perm_singleton_singleton] at h1 h2
  apply List.Perm.cons_inv at h1
  apply List.Perm.cons_inv at h2

  exact ⟨h1, h2, h3⟩

lemma EnvStep_inv_link {𝒢 ℋ : HyperEnv} {x y : FPName}
  (hnd : 𝒢.Nodup) (hES : 𝒢 -[x⟷ₗy]->ₑ ℋ) :
  ∃ 𝒢ᵣ A, (𝒢 ~ 𝒢ᵣ |ₕ [[x ∶ Aᗮ, y ∶ A]]) ∧ (ℋ ~ 𝒢ᵣ) := by
  generalize hl : (x⟷ₗy) = l at hES
  induction hES <;> try contradiction

  case link₁ z w A =>
    use ∅
    simp at ⊢
    injection hl with h1 h2
    subst h1 h2
    use A

  case par₁ 𝒥 𝒥' 𝒦 lbl hES hFl ih =>
    simp at hnd
    obtain ⟨𝒥ᵣ, A, hPᵣ, hP'⟩ := ih hnd.1 hl
    use (𝒥ᵣ |ₕ 𝒦), A
    constructor
    · apply HyperEnv.Perm_rotate_rhs_right
      apply HyperEnv.Perm_merge_cancel_right_inv
      · apply HyperEnv.Perm.trans
        · exact hPᵣ
        · apply HyperEnv.Perm.merge_comm
    · exact HyperEnv.Perm.merge hP' (by rfl)

  case par₂ 𝒦 𝒥 𝒥' lbl hES hFl ih =>
    simp at hnd
    obtain ⟨𝒥ᵣ, A, hPᵣ, hP'⟩ := ih hnd.2 hl
    use (𝒦 |ₕ 𝒥ᵣ), A
    constructor
    · rw [HyperEnv.merge_assoc]
      apply HyperEnv.Perm_merge_cancel_left_inv
      exact hPᵣ
    · exact HyperEnv.Perm.merge (by rfl) hP'

  case res 𝒥 𝒥' Γ Γ' Δ Δ' z w A lbl hFz hFw hFz' hFw' hFlz hFlw hneq hES ih =>
    simp [- Env.mem_pair_fst_in_names_iff, - Env.not_mem_names_iff,
      - Lbl.f, - Lbl.i, Env.Nodup_merge_iff] at hFz hFz' hFw hFw' hFlz hFlw hnd
    rw [HyperEnv.Nodup_merge, HyperEnv.Nodup_merge, HyperEnv.Nodup_cons_iff hFz.2.1,
      HyperEnv.Nodup_cons_iff hFw.2.2] at ih
    simp only [HyperEnv.Nodup_singleton, Env.Nodup_singleton, true_and] at ih
    have ⟨𝒥ᵣ, B, hPᵣ, hP'⟩ := ih ⟨⟨hnd.1, hnd.2.1⟩, hnd.2.2.1⟩ hl
    refine ⟨𝒥' |ₕ [Γ'‚ Δ'], B, ?_, HyperEnv.Perm.refl _⟩

    subst hl
    simp [← ne_eq] at hFlz hFlw

    have ⟨hPΓ', hPΔ', hP𝒥'⟩ := HyperEnv.Perm.extract_link_res
      (hP'.symm.exchange_rhs_left hPᵣ) hFz' hFw' hFlz.1 hFlz.2 hFlw.1 hFlw.2 hneq

    apply HyperEnv.Perm_rotate_rhs_right
    apply HyperEnv.Perm.merge
    · exact hP𝒥'.trans HyperEnv.Perm.merge_comm
    · exact HyperEnv.Perm_singleton_singleton.mpr (List.Perm.append hPΓ' hPΔ')

  case perm 𝒥 𝒥' 𝒦 𝒦' lbl hP hES hP' ih =>
    have ⟨𝒥ᵣ, A, hP𝒥, hP𝒥'⟩ := ih ((HyperEnv.Nodup_perm_iff hP).mpr hnd) hl
    use 𝒥ᵣ, A
    constructor
    · exact hP.symm.trans hP𝒥
    · exact hP'.symm.trans hP𝒥'








-- FIXME:
lemma EnvStep_inv_res_shape {𝒢 ℋ' : HyperEnv} {Γ Δ : Env} {x y : FPName} {A : Types} {l : Lbl}
  (hnd : (𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]).Nodup)
  (hES : 𝒢 |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] -[l]->ₑ ℋ')
  (hx : x ∉ l.i ∪ l.f)
  (hy : y ∉ l.i ∪ l.f)
  (hneq : x ≠ y) :
  ∃ 𝒢' Γ' Δ', ℋ' ~ 𝒢' |ₕ [x ∶ A :: Γ'] |ₕ [y ∶ Aᗮ :: Δ'] := by



  sorry










-- FIXME: Check that this covers all rules mentioned in the paper
-- FIXME: Subject reduction / simulation proof
theorem session_fidelity {n : Nat} {P P' : Proc} {𝒢 : HyperEnv} {l : Lbl} :
  Typing n P 𝒢 → ProcStep P l P' →
  ∃ 𝒢', EnvStep 𝒢 l 𝒢' ∧ Typing n P' 𝒢' := by
  intros hT hPS
  induction hPS generalizing n 𝒢

  -- case one =>
  --   obtain ⟨hP, 𝒟⟩ := Typing_inv_one hT
  --   use ∅
  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · exact EnvStep.one
  --     · exact HyperEnv.Perm.nil
  --   · exact 𝒟

  -- case bot =>
  --   obtain ⟨Γ, hP, 𝒟⟩ := Typing_inv_bot hT
  --   use [Γ]
  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · exact EnvStep.bot
  --     · apply HyperEnv.Perm.refl
  --   · exact 𝒟

  -- case tensor Q x y hF =>
  --   obtain ⟨A, B, Γ, Δ, L, hP, 𝒟⟩ := Typing_inv_tensor hT
  --   use ([y ∶ A :: Γ] |ₕ [x ∶ B :: Δ])

  --   have := Typing.f_eq_names hT
  --   simp_rw [HyperEnv.names_eq_of_perm hP] at this
  --   simp [Channel.f] at this hF
  --   have h : HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ] = insert x (Γ.names ∪ Δ.names) := by simp

  --   have hFy : y ∉ HyperEnv.names [x ∶ A ⨂ B :: Γ‚ Δ] := by
  --     simp [h, ← this, hF]
  --   simp at hFy
  --   obtain ⟨hFy1, hFy2, hFy3⟩ := hFy

  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · exact EnvStep.tensor (by simp [hFy1, hFy2, hFy3])
  --     · simp [HasPerm.perm]
  --   · obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {x, y} ∪ Γ.names ∪ Δ.names ∪ Q.f)
  --     simp at hz
  --     obtain ⟨hnzx, hnzy, hz1, hz2, hz3, hz4⟩ := hz
  --     have 𝒟' := Typing_substNames (x := z) (y := y) (𝒟 z hz1) (by
  --       intros Γ hΓ T hinΓ
  --       simp at hΓ
  --       rcases hΓ with rfl | rfl
  --       case inl =>
  --         simp at hinΓ
  --         rcases hinΓ with ⟨rfl, rfl⟩ | h1
  --         case inl => rfl
  --         case inr =>
  --           have := hFy2 T
  --           contradiction
  --       case inr =>
  --         simp at hinΓ
  --         rcases hinΓ with ⟨rfl, rfl⟩ | h00
  --         case inl => contradiction
  --         case inr =>
  --           have := hFy3 T
  --           contradiction
  --       )
  --     simp [← Proc.open_substNames_intro (z := y) hz4] at 𝒟'

  --     rw [FPName.subst_self_of_ne, Env.substNames_of_not_mem, Env.substNames_of_not_mem] at 𝒟'
  --     · exact 𝒟'
  --     · rw [Env.mem_pair_fst_in_names_iff]
  --       intro ⟨T, hT⟩
  --       exact hz3 T hT
  --     · rw [Env.mem_pair_fst_in_names_iff]
  --       intro ⟨T, hT⟩
  --       exact hz2 T hT
  --     · intro heq
  --       exact hnzx heq.symm

  -- case parr Q x y hF =>
  --   obtain ⟨A, B, Γ, L, hP, 𝒟⟩ := Typing_inv_parr hT
  --   use [y ∶ A :: x ∶ B :: Γ]

  --   have := Typing.f_eq_names hT
  --   simp_rw [HyperEnv.names_eq_of_perm hP] at this
  --   simp [Channel.f] at this hF
  --   have h : HyperEnv.names [x ∶ A ⅋ B :: Γ] = insert x (Γ.names) := by simp

  --   have hFy : y ∉ HyperEnv.names [x ∶ A ⅋ B :: Γ] := by
  --     simp [h, ← this, hF]
  --   simp at hFy
  --   obtain ⟨hneq, hFy⟩ := hFy

  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · exact EnvStep.parr (by simp [hneq, hFy])
  --     · simp [HasPerm.perm]
  --   · obtain ⟨z, hz⟩ := exists_one_fresh (L ∪ {x, y} ∪ Γ.names ∪ Q.f)
  --     simp at hz
  --     obtain ⟨hnzx, hnzy, hz1, hz2, hz3⟩ := hz
  --     have 𝒟' := Typing_substNames (x := z) (y := y) (𝒟 z hz1) (by
  --       intros Γ hΓ T hinΓ
  --       simp at hΓ
  --       subst hΓ
  --       rcases hinΓ
  --       case head => contradiction
  --       case tail hMem =>
  --         cases hMem
  --         case head => contradiction
  --         case tail hMem =>
  --           cases hMem
  --           case head Γ =>
  --             exfalso
  --             apply hFy T
  --             exact List.mem_cons_self
  --           case tail e Γ hMem =>
  --             exfalso
  --             apply hFy T
  --             apply List.mem_cons_of_mem
  --             exact hMem
  --       )

  --     rw [← Proc.open_substNames_intro] at 𝒟'
  --     · simp at 𝒟'
  --       rw [FPName.subst_self_of_ne, Env.substNames_of_not_mem] at 𝒟'
  --       · exact 𝒟'
  --       · rw [Env.mem_pair_fst_in_names_iff]
  --         intro ⟨T, hT⟩
  --         exact hz2 T hT
  --       · rw [← ne_eq] at hnzx
  --         exact hnzx.symm
  --     · exact hz3

  -- case par₁ hFl ih =>
  --   obtain ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
  --   obtain ⟨ℋ₁', hStep, hTP'⟩:= ih hTP
  --   use ℋ₁' |ₕ ℋ₂
  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · apply EnvStep.par₁ hStep
  --       rw [Typing.f_eq_names hTQ] at hFl
  --       exact hFl
  --     · apply HyperEnv.Perm.refl
  --   · apply Typing.mix ?_ hTP' hTQ
  --     rw [← Finset.disjoint_iff_inter_eq_empty, (Typing.f_eq_names hTQ)] at hFl
  --     have hD := Typing_preserves_disjointness (Typing.exchange_hyper hT hP)
  --     exact EnvStep.preserves_disjoint hStep (HyperEnv.disjoint_split hD) hFl

  -- case par₂ hFl ih =>
  --   obtain ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
  --   obtain ⟨ℋ₂', hStep, hTQ'⟩:= ih hTQ
  --   use ℋ₁ |ₕ ℋ₂'
  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · apply EnvStep.par₂ hStep
  --       rw [Typing.f_eq_names hTP] at hFl
  --       exact hFl
  --     · apply HyperEnv.Perm_refl
  --   · apply Typing.mix ?_ hTP hTQ'
  --     rw [← Finset.disjoint_iff_inter_eq_empty, (Typing.f_eq_names hTP)] at hFl
  --     have hD := Typing_preserves_disjointness (Typing.exchange_hyper hT hP)
  --     exact (EnvStep.preserves_disjoint hStep (HyperEnv.disjoint_split hD).symm hFl).symm

  -- case syn l l' _ _ hFl lwf ihP ihQ =>
  --   have ⟨ℋ₁, ℋ₂, hP, hTP, hTQ⟩ := Typing_inv_par hT
  --   have ⟨ℋ₁', hStepP, hTP'⟩ := ihP hTP
  --   have ⟨ℋ₂', hStepQ, hTQ'⟩ := ihQ hTQ
  --   use ℋ₁' |ₕ ℋ₂'
  --   constructor
  --   · apply EnvStep.perm hP.symm
  --     · apply EnvStep.syn hStepP hStepQ
  --       · simp only [Proc.f, HyperEnv.names_merge] at hFl ⊢
  --         rw [(Typing.f_eq_names hTP), (Typing.f_eq_names hTQ)] at hFl
  --         exact hFl
  --       · exact lwf
  --     · simp
  --   · apply Typing.mix ?_ hTP' hTQ'
  --     have := Typing.exchange_hyper hT hP
  --     have := Typing_preserves_disjointness this
  --     have hD := HyperEnv.disjoint_split this
  --     have := EnvStep.preserves_disjoint hStepP hD

  --     rw [Proc.f_par, (Typing.f_eq_names hTP), (Typing.f_eq_names hTQ)] at hFl
  --     rw [← Finset.disjoint_iff_inter_eq_empty] at hFl
  --     have hD_split := Finset.disjoint_union_right.mp hFl

  --     have hD𝒢'ℋ := EnvStep.preserves_disjoint
  --       hStepP hD (Disjoint.mono_left (by simp) hD_split.2)

  --     have hDl'𝒢': Disjoint (Lbl.act l').i ℋ₁'.names :=
  --       have : Disjoint (Lbl.act l').i (ℋ₁.names ∪ (Lbl.act l).i) := by
  --         rw [Finset.disjoint_union_right]
  --         constructor
  --         · exact Disjoint.mono_left (by simp) hD_split.1
  --         · symm
  --           simp only [Finset.disjoint_iff_inter_eq_empty]
  --           exact lwf
  --       Disjoint.mono_right (EnvStep.names_subset hStepP) this

  --     exact (EnvStep.preserves_disjoint hStepQ hD𝒢'ℋ.symm hDl'𝒢').symm

  -- case res Q Q' lbl L hQS ih =>
  --   obtain ⟨A, Γ, Δ, ℋ, L', hP', hT'⟩ := Typing_inv_res hT
  --   obtain ⟨x, y, hx, hy, hneq⟩ :=
  --     exists_two_fresh (L ∪ L' ∪ ℋ.names ∪ Γ.names ∪ Δ.names ∪ lbl.i ∪ lbl.f ∪ Q'.f)
  --   simp only [Finset.union_assoc, Finset.mem_union, not_or] at hx hy
  --   specialize hT' x hx.2.1 y hy.2.1 hneq
  --   obtain ⟨ℋ', hESℋ', hTℋ'⟩ := ih x hx.1 y hy.1 hneq hT'

  --   have hnd : (ℋ |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ]).Nodup :=
  --     (Typing_preserves_linearity hT').1

  --   have hFlblx: x ∉ lbl.i ∪ lbl.f := by
  --     simp [- Lbl.f, - Lbl.i]
  --     exact ⟨hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1⟩

  --   have hFlbly : y ∉ lbl.i ∪ lbl.f := by
  --     simp [- Lbl.f, - Lbl.i]
  --     exact ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩

  --   obtain ⟨ℋᵣ, Γ', Δ', hPℋᵣ⟩ :=
  --     EnvStep_inv_res_shape hnd hESℋ' hFlblx hFlbly hneq

  --   have hFxy := HyperEnv.fresh_of_linear_res hTℋ' hPℋᵣ
  --   refine ⟨ℋᵣ |ₕ [Γ'‚ Δ'], ?_, ?_⟩
  --   · apply EnvStep.perm hP'.symm
  --     · apply EnvStep.res (𝒢 := ℋ) (𝒢' := ℋᵣ) (Γ := Γ) (Γ' := Γ')
  --         (Δ := Δ) (Δ' := Δ') (x := x) (y := y) (A := Aᗮ)
  --       · simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Env.names_merge,
  --           Finset.notMem_union]
  --         exact ⟨hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1⟩
  --       · simp only [HyperEnv.names_merge, HyperEnv.names_singleton, Env.names_merge,
  --           Finset.notMem_union]
  --         exact ⟨hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1⟩
  --       · simp only [HyperEnv.names_merge, HyperEnv.names_singleton,
  --           Env.names_merge, Finset.notMem_union]
  --         exact hFxy.1
  --       · simp only [HyperEnv.names_merge, HyperEnv.names_singleton,
  --           Env.names_merge, Finset.notMem_union]
  --         exact hFxy.2
  --       · exact hFlblx
  --       · exact hFlbly
  --       · exact hneq
  --       · have := EnvStep.perm (HyperEnv.Perm.refl _) hESℋ' hPℋᵣ
  --         simp at this ⊢
  --         exact this
  --     · rfl


  --   · rcases hFxy.1 with ⟨hx1, hx2, hx3⟩
  --     rcases hFxy.2 with ⟨hy1, hy2, hy3⟩
  --     exact Typing_res_exists
  --       ⟨hx1, hx2, hx3, hx.2.2.2.2.2.2.2⟩ ⟨hy1, hy2, hy3, hy.2.2.2.2.2.2.2⟩
  --       hneq (Typing.exchange_hyper hTℋ' hPℋᵣ)


  -- case one_bot Q Q' L hQS ih =>
  --   obtain ⟨A, Γ, Δ, ℋ, L', hP', hT'⟩ := Typing_inv_res hT
  --   obtain ⟨x, y, hx, hy, hneq⟩ := exists_two_fresh (L ∪ L')
  --   simp at hx hy
  --   specialize hT' x hx.2 y hy.2 hneq
  --   obtain ⟨ℋ', hES, hTg⟩ := ih x hx.1 y hy.1 hneq hT'

  --   obtain ⟨hnd, hpw⟩ := (Typing_preserves_linearity hT')
  --   obtain ⟨ℋᵣ, Γᵣ, h_pre, h_post⟩ := EnvStep_inv_one_bot hnd hES

  --   simp only [HyperEnv.PairwiseDisjoint] at hpw

  --   have hnd' := HyperEnv.Nodup_perm h_pre hnd
  --   have hpw' := (HyperEnv.Perm_PairwiseDisjoint_iff h_pre).mp hpw

  --   have hxin : (x ∶ A :: Γ) ∈ ℋ |ₕ [x ∶ A :: Γ] |ₕ [y ∶ Aᗮ :: Δ] := by simp
  --   obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre.symm hxin
  --   simp only [List.mem_append, List.mem_singleton] at hE
  --   rcases hE with h | rfl | rfl
  --   · cases h
  --     case inl h =>
  --       exfalso
  --       have hEx : (x, A) ∈ E := by
  --         simp [HasPerm.perm] at hPE
  --         exact hPE.mem_iff (a := x ∶ A).mpr (by simp)
  --       have hin := (HyperEnv.subset_names_of_mem h) (Env.mem_pair_fst_in_names _ hEx)

  --       have hnin : x ∉ ℋᵣ.names := by
  --         intro hin
  --         have h1 := (List.pairwise_append.mp (List.pairwise_append.mp hpw').1).2.2
  --         have h2 := Env.mem_pair_fst_in_names _ hEx
  --         exact Finset.disjoint_left.mp (h1 E h [x ∶ 1] (by simp)) h2 (by simp)

  --       exact hnin hin
  --     case inr h =>
  --       subst h
  --       simp [HasPerm.perm] at hPE
  --       obtain ⟨h1, h2⟩ := hPE
  --       subst h1 h2

  --       refine ⟨ℋ', ?_, hTg⟩

  --       have hPℋ : ℋ' ~ ℋ |ₕ [Δ] := by
  --           have hin : (y ∶ ⊥ :: Δ) ∈ ℋ |ₕ [[x ∶ 1]] |ₕ [y ∶ 1ᗮ :: Δ] := by
  --             simp
  --             apply Or.inr
  --             rfl

  --           obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre.symm hin

  --           have hΔΓᵣ : Δ ~ Γᵣ := by
  --             simp only [List.mem_append, List.mem_singleton] at hE
  --             rcases hE with h | rfl | rfl
  --             · cases h
  --               case inl h =>
  --                 exfalso
  --                 simp [HasPerm.perm] at hPE

  --                 have hEy : y ∈ E.names := by
  --                   have this : y ∈ Env.names (y ∶ ⊥ :: Δ) := by simp
  --                   rw [← Env.names_eq_of_perm hPE] at this
  --                   exact this

  --                 have hy : y ∈ Env.names (y ∶ ⊥ :: Γᵣ) := by simp
  --                 have h_split := List.pairwise_append.mp hpw'
  --                 have hE : E ∈ ℋᵣ |ₕ [[x ∶ 1]] := List.mem_append_left _ h
  --                 have hDEy : Env.disjoint E (y ∶ ⊥ :: Γᵣ) := by
  --                   apply h_split.2.2 E hE (y ∶ ⊥ :: Γᵣ) (by simp)

  --                 exact Finset.disjoint_left.mp hDEy hEy hy

  --               case inr h =>
  --                 subst h
  --                 simp [HasPerm.perm] at hPE
  --             · simp [HasPerm.perm] at hPE
  --               exact hPE.symm

  --           have hPℋℋᵣ : ℋ ~ ℋᵣ := by
  --             have hPy : ([y ∶ ⊥ :: Γᵣ] : HyperEnv) ~ [y ∶ ⊥ :: Δ] :=
  --               HyperEnv.Perm.cons (List.Perm.cons (y, ⊥) hΔΓᵣ.symm) (HyperEnv.Perm.refl _)

  --             have hP1 := HyperEnv.Perm.merge (HyperEnv.Perm.refl (ℋᵣ |ₕ [[x ∶ 1]])) hPy
  --             have hP2 := (HyperEnv.Perm_merge_cancel_right (h_pre.trans hP1))

  --             exact HyperEnv.Perm_merge_cancel_right hP2

  --           have : ℋᵣ |ₕ [Γᵣ] ~ ℋ |ₕ [Δ] :=
  --             HyperEnv.Perm.merge hPℋℋᵣ.symm (HyperEnv.Perm.cons hΔΓᵣ.symm (.refl _))

  --           exact h_post.trans this
  --       apply EnvStep.perm hP'.symm
  --       · apply EnvStep.one_bot (x := x) (y := y)
  --         · exact EnvStep.perm (HyperEnv.Perm.refl _) hES hPℋ
  --       · simp [hPℋ.symm]

  --   · exfalso
  --     have hxin : (x, A) ∈ y ∶ ⊥ :: Γᵣ :=
  --       (List.Perm.mem_iff hPE).mpr (by simp)
  --     simp only [List.mem_cons] at hxin
  --     rcases hxin with hhd | htl
  --     · injection hhd with heq _
  --       exact hneq heq
  --     · have hx_name : x ∈ Env.names (y ∶ ⊥ :: Γᵣ) := by
  --         have h_in_env : (x, A) ∈ y ∶ ⊥ :: Γᵣ := List.mem_cons_of_mem _ htl
  --         exact Env.mem_pair_fst_in_names _ h_in_env

  --       have hxin : x ∈ Env.names [x ∶ 1] := by simp
  --       have hpw'_split := (List.pairwise_append.mp hpw').2.2

  --       have h_disj_x_y : Env.disjoint [x ∶ 1] (y ∶ ⊥ :: Γᵣ) := by
  --         have hxin' : [x ∶ 1] ∈ ℋᵣ |ₕ [[x ∶ 1]] := by simp
  --         apply hpw'_split [x ∶ 1] hxin' (y ∶ ⊥ :: Γᵣ) (by simp)

  --       exact Finset.disjoint_left.mp h_disj_x_y hxin hx_name


-- FIXME:
  -- case tensor_parr => sorry



  -- case disp₁ x =>
  --   obtain ⟨Γ, A, hP', hT', hF⟩ := Typing_inv_disp₁ hT
  --   use [x ∶ ⊥ :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm EnvStep.disp₁ (by simp)
  --   · exact Typing.bot hF hT'

  -- case disp₂ P x =>
  --   obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
  --   use [x ∶ 1 :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm EnvStep.disp₂ (by simp)
  --   · have ⟨hNodup, _ ⟩:= Typing_preserves_linearity hT'
  --     have hNodupxΓ := hNodup (x ∶ A :: Γ) (by simp)
  --     obtain ⟨hxΓ, hNodupΓ⟩:= (Env.Nodup_cons.mp hNodupxΓ)
  --     have hNodup_names : ((P.f.erase x).toList).Nodup := Finset.nodup_toList _

  --     have heq : Env.names Γ = ((P.f.erase x).toList).toFinset := by
  --       ext a
  --       simp only [List.mem_toFinset, Finset.mem_toList, Finset.mem_erase]

  --       have hPf : P.f = Env.names (x ∶ A :: Γ) := by
  --         have := Typing.f_eq_names hT'
  --         simp only [HyperEnv.names_singleton] at this
  --         exact this

  --       rw [hPf]
  --       simp only [Env.names, List.map_cons, List.toFinset_cons, Finset.mem_insert]
  --       constructor
  --       · intro ha
  --         have h_neq : a ≠ x := by
  --           rintro rfl
  --           exact hxΓ ha
  --         exact ⟨h_neq, Or.inr ha⟩
  --       · rintro ⟨hneq, rfl | ha⟩
  --         · contradiction
  --         · exact ha

  --     have hlc : Env.lc n Γ := by
  --       have h_in_singleton : (x ∶ !!A :: Γ) ∈ [x ∶ !!A :: Γ] := by simp
  --       obtain ⟨Γ', hin𝒢, hP''⟩ := HyperEnv.Perm_mem hP' h_in_singleton
  --       have hlcΓ := Typing_preserves_lc_context hT Γ' hin𝒢
  --       have hlcAΓ := (Env.lc_perm hP'').mp hlcΓ
  --       have := (Env.lc_cons.mp hlcAΓ).2
  --       exact this

  --     exact ProcStep_buildDisp Γ _ hServ hNodup_names heq hxΓ hlc hNodupΓ

  -- case dup₁ x =>
  --   obtain ⟨Γ, A, L, hP', hF, hT'⟩ := Typing_inv_dup₁ hT
  --   use [x ∶ ??A ⅋ ??A :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm EnvStep.dup₁ (by simp)
  --   · apply Typing.parr ?_ (L ∪ {x})
  --     · simp at ⊢ hT'
  --       intros z hneq hin
  --       specialize hT' z hin hneq
  --       exact hT'
  --     · exact hF

  -- case dup₂ Q z =>
  --   obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
  --   use [z ∶ !!A ⨂ !!A :: Γ]
  --   · constructor
  --     · exact EnvStep.perm hP'.symm (EnvStep.dup₂ hServ) (by rfl)
  --     · apply ProcStep_buildDup (names := (Q.f.erase z).toList)
  --       · exact hServ
  --       · simp
  --         rw [Typing.f_eq_names hT']
  --         have hnd := (Typing_preserves_linearity hT').1
  --         simp [HyperEnv.Nodup, Env.Nodup_cons] at ⊢ hnd
  --         exact hnd.1
  --       · exact Finset.nodup_toList _
  --       · exact hT'

  -- case use₁ x =>
  --   obtain ⟨Γ, A, hP', hT'⟩ := Typing_inv_use₁ hT
  --   use [x ∶ A :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm EnvStep.use₁ (by simp)
  --   · exact hT'

  -- case use₂ x =>
  --   obtain ⟨Γ, A, hP', hT', hServ⟩ := Typing_inv_use₂ hT
  --   use [x ∶ A :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm (EnvStep.use₂ hServ) (by simp)
  --   · exact hT'

  -- case output x A =>
  --   obtain ⟨Γ, B, hP', hT'⟩ := Typing_inv_output hT
  --   use [x ∶ B{A // 0} :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm EnvStep.output (by simp)
  --   · exact hT'

  -- case input x A hlc =>
  --   obtain ⟨Γ, B, hP', hT'⟩ := Typing_inv_input hT
  --   use [x ∶ B{A // 0} :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP'.symm (EnvStep.input hlc) (by simp)
  --   · have := Typing_substTypes hT' (k := 0) (A := A)
  --     simp at this
  --     exact this (Types.lc_mono hlc)

  -- case selectL x =>
  --   obtain ⟨Γ, A, B, hP, hT⟩ := Typing_inv_selectL hT
  --   use [x ∶ A :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP.symm EnvStep.selectL (by simp)
  --   · exact hT

  -- case selectR x =>
  --   obtain ⟨Γ, A, B, hP, hT⟩ := Typing_inv_selectR hT
  --   use [x ∶ B :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP.symm EnvStep.selectR (by simp)
  --   · exact hT

  -- case ampL x =>
  --   obtain ⟨Γ, A, B, hP, hTP, hTQ⟩ := Typing_inv_amp hT
  --   use [x ∶ A :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP.symm EnvStep.ampL (by simp)
  --   · exact hTP

  -- case ampR x =>
  --   obtain ⟨Γ, A, B, hP, hTP, hTQ⟩ := Typing_inv_amp hT
  --   use [x ∶ B :: Γ]
  --   constructor
  --   · exact EnvStep.perm hP.symm EnvStep.ampR (by simp)
  --   · exact hTQ

  -- case link₁ =>
  --   obtain ⟨A, hP⟩ := Typing_inv_link hT
  --   use ∅
  --   constructor
  --   · exact EnvStep.perm hP.symm (EnvStep.link₁) (by simp)
  --   · apply Typing.mix₀

  -- case link₂ x y =>
  --   obtain ⟨A, hP⟩ := Typing_inv_link hT
  --   use ∅
  --   constructor
  --   · have := HyperEnv.swap_two_inner (x := y) (y := x) (A := Aᗮᗮ) (B := Aᗮ)
  --     conv at this => rhs ; rw [Types.dual_involution]
  --     have := HyperEnv.Perm.trans hP this.symm
  --     apply EnvStep.perm this.symm
  --     · exact EnvStep.link₁
  --     · simp [HasPerm.perm]
  --   · apply Typing.mix₀


-- FIXME:
  case com => sorry

  all_goals sorry


  -- case axcut Q Q' x L hPS ih =>
  --   have ⟨A, Γ, Δ, 𝒢', L', hP', hT'⟩ := Typing_inv_res hT
  --   have ⟨z, w, hz, hw, hzw⟩ := exists_two_fresh (L ∪ L' ∪ {x} ∪ 𝒢'.names ∪ Q'.f)
  --   simp [← ne_eq] at hz hw
  --   specialize hT' z hz.2.2.1 w hw.2.2.1 hzw
  --   obtain ⟨ℋ, hESℋ, hTℋ⟩ := ih z hz.2.1 w hw.2.1 hzw hT'

  --   have hlin := Typing_preserves_linearity hT'
  --   have ⟨hnd, hpw⟩ := hlin

  --   obtain ⟨ℋᵣ, B, h_pre, h_post⟩ := EnvStep_inv_link hnd hESℋ

  --   have h_pre' := by
  --     have : ℋᵣ |ₕ [[x ∶ Bᗮ, z ∶ B]] ~ ℋ |ₕ [[x ∶ Bᗮ, z ∶ B]] := by
  --       apply HyperEnv.Perm.merge
  --       · exact h_post.symm
  --       · rfl
  --     exact h_pre.trans this

  --   have hlin' := (HyperEnv.Perm_preserves_Linearity h_pre').mp hlin

  --   have hQf := Typing.f_eq_names hTℋ

  --   have hFxℋ : x ∉ ℋ.names := by
  --     simp at hlin'
  --     rw [HyperEnv.not_mem_names_iff]
  --     intros E T hE
  --     have ⟨_, hxℋ⟩ := hlin'.2.2 E hE
  --     exact hxℋ T

  --   have hFzℋ : z ∉ ℋ.names := by
  --     simp at hlin'
  --     rw [HyperEnv.not_mem_names_iff]
  --     intros E T hE
  --     have ⟨hzℋ, _⟩ := hlin'.2.2 E hE
  --     exact hzℋ T

  --   have hT_subst' : n ⊢ Q'⸨#z, #w⸩{x // z}{x // w} ∷ ℋ{x // z}{x // w} := by
  --     have hT_subst : n ⊢ Q'⸨#z, #w⸩{x // z} ∷ ℋ{x // z} := by
  --       apply Typing_substNames hTℋ
  --       intro E hEℋ C hinE
  --       exfalso
  --       exact hFxℋ (HyperEnv.mem_of_mem_mem_names hinE hEℋ)

  --     apply Typing_substNames hT_subst
  --     intro E hEℋ C hinE
  --     exfalso
  --     rw [HyperEnv.substNames_of_not_mem (y := x) hFzℋ] at hEℋ
  --     exact hFxℋ (HyperEnv.mem_of_mem_mem_names hinE hEℋ)

  --   use ℋ{x // z}{x // w}
  --   simp [Proc.open_two_substNames, FPName.subst_self, FPName.subst_self_of_ne hzw.symm,
  --     FPName.subst_self_of_ne hw.1.symm] at hT_subst'

  --   have hFwQ : w ∉ Q'{x // z}.f := by
  --     rw [Proc.substNames_of_not_mem hz.2.2.2.2]
  --     exact hw.2.2.2.2

  --   rw [Proc.substNames_of_not_mem hFwQ, Proc.substNames_of_not_mem hz.2.2.2.2] at hT_subst'

  --   constructor
  --   · rw [HyperEnv.substNames_of_not_mem hFzℋ]

  --     have hzin : z ∶ A :: Γ ∈ 𝒢' |ₕ [z ∶ A :: Γ] |ₕ [w ∶ Aᗮ :: Δ] := by simp
  --     obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre.symm hzin
  --     simp only [List.mem_append, List.mem_singleton] at hE
  --     rcases hE with h | rfl
  --     · exfalso
  --       have hzE: (z, A) ∈ E := ((List.Perm.mem_iff hPE).mpr (by simp))
  --       have hz_names := (HyperEnv.mem_of_mem_mem_names (x := z) (A := A) hzE h)
  --       rw [← HyperEnv.names_eq_of_perm h_post] at hz_names
  --       exact hFzℋ hz_names
  --     · have hzAin : (z, A) ∈ [(x, Bᗮ), (z, B)] :=
  --         (List.Perm.mem_iff (a := (z, A)) hPE).mpr (by simp)

  --       simp only [List.mem_cons] at hzAin
  --       rcases hzAin with hzx | hzz
  --       · obtain ⟨rfl, rfl⟩ := hzx
  --         simp at hz
  --       · simp at hzz
  --         subst hzz

  --         have hPΓ : [(x, Aᗮ)] ~ Γ := List.Perm.cons_inv ((List.Perm.swap ..).trans hPE)

  --         symm at h_pre
  --         apply HyperEnv.Perm_rotate_rhs_left at h_pre

  --         have h1 : [w ∶ Aᗮ :: Δ] |ₕ 𝒢' |ₕ [z ∶ A :: Γ] ~
  --           [w ∶ Aᗮ :: Δ] |ₕ 𝒢' |ₕ [x ∶ Aᗮ :: [z ∶ A]] := by
  --           apply HyperEnv.Perm.merge_left
  --           apply HyperEnv.Perm.cons
  --           · exact hPE.symm
  --           · rfl

  --         have h2 := h_post.trans (HyperEnv.Perm_merge_cancel_right (h_pre.trans h1))
  --         have h3 := HyperEnv.substNames_preserves_perm (x := w) (y := z) h2
  --         simp at h3

  --         -- FIXME: May need to add a rule to be able to deal with ProcStep.axcut. The discrepancy
  --         -- is probably from not following the paper exactly and proving session fidelity using
  --         -- ProcStep (look into this, maybe look at forwarder theory, or congruence theory)
  --         -- | link_res
  --         --       {𝒢 ℋ : HyperEnv} {Γ Δ : Env} {x z w : FPName} {A : Types} :
  --         --       EnvStep (𝒢 |ₕ [z ∶ A :: Γ] |ₕ [w ∶ Aᗮ :: Δ]) (x ⟷ₗ z) ℋ →
  --         --       -------------------------------------------------------------
  --         --       EnvStep (𝒢 |ₕ [Γ‚ Δ]) (τ) (ℋ{x // w})
  --         sorry

  --   · exact hT_subst'
