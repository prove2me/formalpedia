-- Prove2me | solution 1 for NeuroSymbolicRLHF.le_sup_p_univ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:03:00.397634+00:00
-- url     : https://prove2.me/submissions/e31c9359-e270-4aae-b76a-a5a2f6cca9a7

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset Real BigOperators in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (i : ι) :
    f i ≤ univ.sup' univ_nonempty f := by
  exact Finset.le_sup' f (Finset.mem_univ i)
