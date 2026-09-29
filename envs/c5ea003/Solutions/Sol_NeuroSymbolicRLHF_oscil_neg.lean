-- Prove2me | solution 1 for NeuroSymbolicRLHF.oscil_neg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:11:32.201757+00:00
-- url     : https://prove2.me/submissions/da5dcad4-b4d8-403f-a646-df4a309796b4

import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    oscil (fun i => -f i) = oscil f := by
  unfold oscil
  -- negation swaps the max and the min
  have h1 : Finset.univ.sup' Finset.univ_nonempty (fun i => -f i)
      = -Finset.univ.inf' Finset.univ_nonempty f := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun i hi => neg_le_neg (Finset.inf'_le f hi)
    · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
      rw [hfi]
      exact Finset.le_sup' (fun i => -f i) hi
  have h2 : Finset.univ.inf' Finset.univ_nonempty (fun i => -f i)
      = -Finset.univ.sup' Finset.univ_nonempty f := by
    apply le_antisymm
    · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
      rw [hfi]
      exact Finset.inf'_le (fun i => -f i) hi
    · exact Finset.le_inf' _ _ fun i hi => neg_le_neg (Finset.le_sup' f hi)
  rw [h1, h2]
  ring
