-- Prove2me | solution 1 for NeuroSymbolicRLHF.oscil_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:12:32.102616+00:00
-- url     : https://prove2.me/submissions/22484c28-5d31-4a0b-96a0-05fe551fe532

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {c : ℝ} (hc : 0 < c) (f : ι → ℝ) :
    oscil (fun i => c * f i) = c * oscil f := by
  have hsup := Finset.comp_sup'_eq_sup'_comp (f := f) (Finset.univ_nonempty (α := ι)) (fun w : ℝ => c * w)
    (fun x y => mul_max_of_nonneg x y hc.le)
  have hinf := Finset.comp_inf'_eq_inf'_comp (f := f) (Finset.univ_nonempty (α := ι)) (fun w : ℝ => c * w)
    (fun x y => mul_min_of_nonneg x y hc.le)
  simp only [oscil, Function.comp] at *
  rw [← hsup, ← hinf]
  ring
