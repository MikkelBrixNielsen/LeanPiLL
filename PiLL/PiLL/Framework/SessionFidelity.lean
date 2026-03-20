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

      exact ProcStep_buildDisp Γ _ hServ hNodup_names heq hxΓ hlc hNodupΓ

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
      · apply ProcStep_buildDup (names := (Q.f.erase z).toList)
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




lemma Env.exists_perm_cons {Γ : Env} {x : FPName} {A : Types} (h : (x, A) ∈ Γ) :
  ∃ Δ, Γ ~ (x, A) :: Δ := by
  induction Γ
  case nil => simp at h
  case cons e Ξ ih =>
    simp at h
    cases h
    case inl h => subst h ; use Ξ
    case inr h =>
      obtain ⟨y, T⟩ := e
      obtain ⟨Ξ', hP⟩ := ih h
      use (y ∶ T :: Ξ)
      sorry






lemma HyperEnv.Perm.extract_bot_res
  {𝒢 ℋ 𝒢ᵣ : HyperEnv} {Γ Γ' Δ Δ' Ξ : Env} {x y z : FPName} {A : Types}
  (h_pre : 𝒢 |ₕ [x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ] ~ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ])
  (h_post : ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] ~ 𝒢ᵣ |ₕ [Ξ])
  (h_zx : z ≠ x) (h_zy : z ≠ y)
  (hFx : x ∉ 𝒢.names) (hFy : y ∉ 𝒢.names)
  (hFx' : x ∉ ℋ.names) (hFy' : y ∉ ℋ.names)
  (hneq : x ≠ y) (hyΓ : y ∉ Γ.names) (hxΔ : x ∉ Δ.names) :
  ∃ 𝒢ᵣ_new Γₙ,
    𝒢 |ₕ [Γ‚ Δ] ~ 𝒢ᵣ_new |ₕ [z ∶ ⊥ :: Γₙ] ∧
    ℋ |ₕ [Γ'‚ Δ'] ~ 𝒢ᵣ_new |ₕ [Γₙ] := by

  have h1 : (z ∶ ⊥ :: Ξ) ∈ 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] := by simp
  obtain ⟨E, hE, hPE⟩ := HyperEnv.Perm_mem h_pre h1
  simp only [List.mem_append, List.mem_singleton] at hE
  rcases hE with h | rfl | rfl
  · rcases h with hE𝒢 | hEΓx
    ·
      obtain ⟨𝒢ᵣ', h𝒢_split⟩ : ∃ 𝒢ᵣ', 𝒢 ~ E :: 𝒢ᵣ' := by
        sorry


      have h𝒢Ξz : 𝒢 ~ (z ∶ ⊥ :: Ξ) :: 𝒢ᵣ' := by
        apply HyperEnv.Perm.trans h𝒢_split
        exact HyperEnv.Perm.cons hPE (HyperEnv.Perm.refl _)

      refine ⟨𝒢ᵣ' |ₕ [Γ‚ Δ], Ξ, ?_, ?_⟩
      · apply HyperEnv.Perm.trans
        · exact HyperEnv.Perm.merge_right h𝒢Ξz [Γ‚ Δ]
        · have := (HyperEnv.Perm_merge_singleton (z ∶ ⊥ :: Ξ) (𝒢ᵣ' |ₕ [Γ‚ Δ])).symm
          rw [HyperEnv.cons_append, ← HyperEnv.merge_assoc] at this
          exact this

      · have h𝒢Ξz' : 𝒢 ~ [z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ' := by
          rw [HyperEnv.cons_append] at h𝒢Ξz
          exact h𝒢Ξz

        have h_pre_subst : 𝒢ᵣ |ₕ [z ∶ ⊥ :: Ξ] ~
          ([z ∶ ⊥ :: Ξ] |ₕ 𝒢ᵣ') |ₕ ([x ∶ Aᗮ :: Γ] |ₕ [y ∶ A :: Δ]) := by
          rw [HyperEnv.merge_assoc] at h_pre
          have := HyperEnv.Perm.exchange_lhs_left h𝒢Ξz' h_pre
          exact this.symm

        apply HyperEnv.Perm_rotate_rhs_right at h_pre_subst
        have hP𝒢ᵣ := HyperEnv.Perm_merge_cancel_right h_pre_subst
        have h_post_subst := HyperEnv.Perm.exchange_rhs_left hP𝒢ᵣ h_post

        conv_rhs at h_post_subst => rw [HyperEnv.merge_assoc]
        apply HyperEnv.Perm_pull_rhs_mid_left at h_post_subst
        apply HyperEnv.Perm_rotate_rhs_left at h_post_subst

        have hEy : y ∶ A :: Δ' ∈ ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] := by simp
        obtain ⟨Ey, hEy', hPEy⟩ := HyperEnv.Perm_mem (h_post_subst.symm) hEy

        have hyA: (y, A) ∈ Ey := by
            simp [HasPerm.perm] at hPEy
            have := hPEy.symm.subset
            simp at this
            exact this.1

        have hyinEy : y ∈ Ey.names := by
          exact Env.mem_pair_fst_in_names _ hyA

        simp only [List.mem_append, List.mem_singleton] at hEy'
        rcases hEy' with h1 | rfl | rfl | rfl
        · cases h1 with
          | inl h1' =>
            cases h1' with
            | inl hin𝒢ᵣ =>
              exfalso
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem hin𝒢ᵣ) hyinEy]

            | inr hEyΞ =>
              exfalso
              symm at hEyΞ
              subst hEyΞ
              apply hFy
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp
              apply Or.inl
              use A
              apply (List.Perm.mem_iff (a := (y, A)) hPE).mpr
              simp
              exact Or.inr hyA

          | inr hEyΓx =>
            exfalso
            symm at hEyΓx
            subst hEyΓx
            simp only [List.mem_cons] at hyA
            rcases hyA with heq | hyinΓ
            · injection heq with heq_name _
              exact hneq heq_name.symm
            · exact hyΓ (Env.mem_pair_fst_in_names _ hyinΓ)

        · have hPΔΔ' : Δ ~ Δ' := by
            simp [HasPerm.perm] at hPEy
            exact hPEy

          have h_post' : ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ] ~
            ℋ |ₕ [x ∶ Aᗮ :: Γ'] |ₕ [y ∶ A :: Δ'] := by
            apply HyperEnv.Perm.merge_exchange_right
            apply HyperEnv.Perm.cons
            · apply List.Perm.cons
              exact hPΔΔ'
            · rfl

          have h_post_no_y :=
            HyperEnv.Perm_merge_cancel_right (h_post_subst.symm.trans h_post'.symm)
          have hx_LHS : x ∶ Aᗮ :: Γ' ∈ ℋ |ₕ [x ∶ Aᗮ :: Γ'] := by simp
          obtain ⟨Ex, hEx_RHS, hPEx⟩ := HyperEnv.Perm_mem h_post_no_y hx_LHS

          have hxA: (x, Aᗮ) ∈ Ex := by
            simp [HasPerm.perm] at hPEx
            have := hPEx.symm.subset
            simp at this
            exact this.1

          have hxinEx : x ∈ Ex.names := by
            exact Env.mem_pair_fst_in_names _ hxA

          simp only [List.mem_append, List.mem_singleton] at hEx_RHS
          rcases hEx_RHS with h1 | hEx_Xi | rfl
          · cases h1 with
            | inl h =>
              exfalso
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp [(HyperEnv.subset_names_of_mem h) hxinEx]

            | inr h =>
              exfalso
              symm at h
              subst h
              apply hFx
              rw [HyperEnv.names_eq_of_perm h𝒢_split]
              simp
              apply Or.inl
              use Aᗮ
              apply (List.Perm.mem_iff (a := (x, Aᗮ)) hPE).mpr
              simp
              exact Or.inr hxA

          · have hPΓΓ' : Γ ~ Γ' := by
              simp [HasPerm.perm] at hPEx
              exact hPEx

            have h_post'' : ℋ |ₕ [x ∶ Aᗮ :: Γ] ~
              ℋ |ₕ [x ∶ Aᗮ :: Γ'] := by
              apply HyperEnv.Perm.merge_exchange_right
              apply HyperEnv.Perm.cons
              · apply List.Perm.cons
                simp [HasPerm.perm] at hPEx
                apply hPEx
              · rfl

            rw [HyperEnv.merge_assoc]
            apply HyperEnv.Perm_pull_rhs_mid_left
            rw [← HyperEnv.merge_assoc]
            apply HyperEnv.Perm_rotate_rhs_left
            apply HyperEnv.Perm.merge
            · exact HyperEnv.Perm_merge_cancel_right (h_post''.trans h_post_no_y.symm)
            · symm
              apply HyperEnv.Perm.cons
              · exact (List.Perm.append_right Δ hPΓΓ').trans
                  (List.Perm.append_left Γ' hPΔΔ')
              · rfl

    · subst hEΓx

      have hzinΓx : (z, ⊥) ∈ x ∶ Aᗮ :: Γ := by
        simp [HasPerm.perm] at hPE
        have h := hPE.symm.subset
        simp at h
        obtain ⟨hL, hR⟩ := h
        cases hL
        case inl hL1 =>
          rw [hL1.1, hL1.2]
          simp
        case inr hL2 =>
          exact List.mem_cons.mpr (Or.inr hL2)


      simp at hzinΓx
      rcases hzinΓx with ⟨hzx, _⟩ | hin
      · subst hzx
        contradiction
      ·
        obtain ⟨Γ_rest, hΓ_split⟩ :=




        sorry









      sorry
  · sorry
