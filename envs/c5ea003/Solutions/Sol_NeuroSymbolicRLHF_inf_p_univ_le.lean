-- Prove2me | solution 1 for NeuroSymbolicRLHF.inf_p_univ_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:07:09.49499+00:00
-- url     : https://prove2.me/submissions/703adad2-20c6-4baf-941e-10f9ca053f5f

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset Real BigOperators in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (i : ι) :
    univ.inf' univ_nonempty f ≤ f i := by
  exact Finset.inf'_le f (Finset.mem_univ i)
