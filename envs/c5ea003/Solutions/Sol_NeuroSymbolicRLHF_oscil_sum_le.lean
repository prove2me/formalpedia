-- Prove2me | solution 1 for NeuroSymbolicRLHF.oscil_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:07:10.763045+00:00
-- url     : https://prove2.me/submissions/ad1cddff-d396-4509-831f-7183f46f37a0

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ → ι → ℝ) (n : ℕ) :
    oscil (fun i => ∑ k ∈ Finset.range n, r k i) ≤ ∑ k ∈ Finset.range n, oscil (r k) := by
  -- oscillation is subadditive: `max (f+g) ≤ max f + max g`, `min (f+g) ≥ min f + min g`
  have hadd : ∀ f g : ι → ℝ, oscil (fun i => f i + g i) ≤ oscil f + oscil g := by
    intro f g
    unfold oscil
    have h1 : univ.sup' univ_nonempty (fun i => f i + g i)
        ≤ univ.sup' univ_nonempty f + univ.sup' univ_nonempty g :=
      Finset.sup'_le _ _ fun i hi => add_le_add (Finset.le_sup' f hi) (Finset.le_sup' g hi)
    have h2 : univ.inf' univ_nonempty f + univ.inf' univ_nonempty g
        ≤ univ.inf' univ_nonempty (fun i => f i + g i) :=
      Finset.le_inf' _ _ fun i hi => add_le_add (Finset.inf'_le f hi) (Finset.inf'_le g hi)
    linarith
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold oscil
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact (hadd _ _).trans (by linarith)
