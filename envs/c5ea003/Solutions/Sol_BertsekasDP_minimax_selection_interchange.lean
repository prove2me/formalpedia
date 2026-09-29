-- Prove2me | solution 1 for BertsekasDP.minimax_selection_interchange
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T21:18:30.9969+00:00
-- url     : https://prove2.me/submissions/601dec26-954b-4b8f-af90-f28e55d4e479

import Mathlib.Data.EReal.Basic

/-- Bertsekas, *Dynamic Programming and Optimal Control* Vol. I, Lemma 1.6.1:
minimization over selection functions commutes with the supremum over
disturbances. -/
theorem solution {W U : Type} (G : W → U → EReal)
    (h : ∀ w, ⨅ u, G w u ≠ ⊥) :
    ⨅ μ : W → U, ⨆ w, G w (μ w) = ⨆ w, ⨅ u, G w u := by
  apply le_antisymm
  · -- Suppose the left side exceeded the right; pick `c` strictly between them.
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, hRc, hcL⟩ := exists_between hlt
    -- For every `w`, the pointwise infimum is below `c`, so some `u` beats `c`.
    have hw : ∀ w, ∃ u, G w u < c := fun w =>
      iInf_lt_iff.mp (lt_of_le_of_lt (le_iSup (fun w => ⨅ u, G w u) w) hRc)
    choose μ hμ using hw
    -- The selection `μ` witnesses that the left side is at most `c`.
    have hle : ⨅ μ : W → U, ⨆ w, G w (μ w) ≤ c :=
      (iInf_le _ μ).trans (iSup_le fun w => (hμ w).le)
    exact absurd (lt_of_lt_of_le hcL hle) (lt_irrefl c)
  · -- Every selection is pointwise at least the pointwise infimum.
    exact le_iInf fun μ => iSup_mono fun w => iInf_le (fun u => G w u) (μ w)
