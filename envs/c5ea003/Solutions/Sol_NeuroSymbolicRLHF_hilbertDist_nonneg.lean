-- Prove2me | solution 1 for NeuroSymbolicRLHF.hilbertDist_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:34:57.935087+00:00
-- url     : https://prove2.me/submissions/ba5e1bf2-9ec0-4cb4-aa27-4b7979f8a1ab

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset Real BigOperators in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → ℝ) :
    0 ≤ hilbertDist p q := by
  -- `oscil g = sup' g - inf' g`, and the infimum never exceeds the supremum
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hle : (Finset.univ.inf' Finset.univ_nonempty (fun j => Real.log (p j / q j)))
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => Real.log (p j / q j)) :=
    le_trans (Finset.inf'_le _ (Finset.mem_univ i))
      (Finset.le_sup' (fun j => Real.log (p j / q j)) (Finset.mem_univ i))
  show 0 ≤ (Finset.univ.sup' Finset.univ_nonempty (fun j => Real.log (p j / q j)))
      - Finset.univ.inf' Finset.univ_nonempty (fun j => Real.log (p j / q j))
  linarith
