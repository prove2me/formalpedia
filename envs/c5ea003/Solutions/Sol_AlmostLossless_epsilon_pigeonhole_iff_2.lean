-- Prove2me | solution 2 for AlmostLossless.epsilon_pigeonhole_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:39:22.574157+00:00
-- url     : https://prove2.me/submissions/c3eb1801-c8e3-4b35-beca-b55987f49354

import Definitions.Def_Logic_AlmostLossless_Core
open AlmostLossless in
theorem solution {S : Type*} {C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    [Nonempty C] (μ : Source S) (ε : ℚ) :
    (∃ K : Code S C, failProb μ K ≤ ε)
      ↔ ∃ T : Finset S, T.card ≤ Fintype.card C ∧ 1 - ε ≤ μ.prob T := by
  have hcorr : ∀ K : Code S C, (({s | Correct K s} : Finset S).card) ≤ Fintype.card C := by
    intro K
    have hinj : Set.InjOn K.enc ({s | Correct K s} : Finset S) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Correct] at hx hy
      have : some x = some y := by rw [← hx, ← hy, hxy]
      exact Option.some.inj this
    have := Finset.card_le_card_of_injOn K.enc (fun x _ => Finset.mem_univ (K.enc x)) hinj
    simpa using this
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨({s | Correct K s} : Finset S), hcorr K, ?_⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset S)
      (fun s => Correct K s) μ.w
    rw [μ.total] at hsplit
    unfold failProb at hK
    unfold Source.prob
    linarith
  · rintro ⟨T, hT, hprob⟩
    classical
    have hcardT : Fintype.card T ≤ Fintype.card C := by simpa using hT
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardT
    let K : Code S C :=
      { enc := fun s => if hs : s ∈ T then e ⟨s, hs⟩ else Classical.arbitrary C
        dec := fun c => if h : ∃ t : T, e t = c then some (Classical.choose h).1 else none }
    refine ⟨K, ?_⟩
    have hcorrT : ∀ s ∈ T, Correct K s := by
      intro s hs
      have hex : ∃ t : T, e t = K.enc s := ⟨⟨s, hs⟩, by simp [K, hs]⟩
      show K.dec (K.enc s) = some s
      simp only [K, dif_pos hex]
      have hspec : e (Classical.choose hex) = K.enc s := Classical.choose_spec hex
      have hKs : K.enc s = e ⟨s, hs⟩ := by simp [K, hs]
      have := e.injective (hspec.trans hKs)
      exact congrArg (fun t : T => some t.1) this
    have hsub : ({s | ¬ Correct K s} : Finset S) ⊆ Tᶜ := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [Finset.mem_compl]
      exact fun hsT => hs (hcorrT s hsT)
    have hle : failProb μ K ≤ ∑ s ∈ Tᶜ, μ.w s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => μ.nonneg s)
    have htot := Finset.sum_compl_add_sum T μ.w
    rw [μ.total] at htot
    unfold Source.prob at hprob
    linarith
