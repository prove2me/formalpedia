-- Prove2me | solution 2 for EmergentGeometry.pairModel_throat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:24:30.510818+00:00
-- url     : https://prove2.me/submissions/c25950a0-2f61-4f9d-a8d4-2b9d2e2d94bf

import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
open EmergentGeometry Finset in
theorem solution (w : ℝ) (hw : 0 ≤ w) :
    throat (pairModel w hw).toBulkGraph (single 0) (single 1) = w ∧
      mutualInfo (pairModel w hw) (single 0) (single 1)
        = 2 * throat (pairModel w hw).toBulkGraph (single 0) (single 1) := by
  -- the two cut weights we need
  have hcw0 : cutWeight (pairModel w hw).toBulkGraph (single (0 : Fin 2)) = w := by
    simp [cutWeight, Fin.sum_univ_two, single, sepBit, pairModel]
  have hcw1 : cutWeight (pairModel w hw).toBulkGraph (single (1 : Fin 2)) = w := by
    simp [cutWeight, Fin.sum_univ_two, single, sepBit, pairModel]
  have hcwall : cutWeight (pairModel w hw).toBulkGraph
      (fun v => single (0 : Fin 2) v || single (1 : Fin 2) v) = 0 := by
    simp [cutWeight, Fin.sum_univ_two, single, sepBit, pairModel]
  -- every region is its own unique admissible surface (there are no interior cells)
  have hent : ∀ A : Region (Fin 2),
      entropy (pairModel w hw) A = cutWeight (pairModel w hw).toBulkGraph A := by
    intro A
    apply le_antisymm
    · exact Finset.inf'_le _ (mem_admSet.mpr (fun v _ => rfl))
    · refine Finset.le_inf' _ _ (fun f hf => ?_)
      have hfa : f = A := by
        funext v
        exact (mem_admSet.mp hf) v rfl
      rw [hfa]
  -- the separating family is the singleton {single 0}
  have hsep : sepSet (single (0 : Fin 2)) (single 1) = {single (0 : Fin 2)} := by
    ext f
    simp only [sepSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Separates, single]
    constructor
    · rintro ⟨h1, h2⟩
      funext x
      fin_cases x
      · simpa using h1 0 (by simp)
      · simpa using h2 1 (by simp)
    · rintro rfl
      refine ⟨fun v hv => hv, fun v hv => ?_⟩
      have : v = 1 := by simpa using hv
      subst this
      decide
  have hne : (sepSet (single (0 : Fin 2)) (single 1)).Nonempty := by
    rw [hsep]
    exact ⟨_, Finset.mem_singleton_self _⟩
  have hmem : single (0 : Fin 2) ∈ sepSet (single 0) (single 1) := by
    rw [hsep]
    exact Finset.mem_singleton_self _
  have hthroat : throat (pairModel w hw).toBulkGraph (single 0) (single 1) = w := by
    unfold throat
    rw [dif_pos hne]
    apply le_antisymm
    · calc (sepSet (single (0 : Fin 2)) (single 1)).inf' hne
            (cutWeight (pairModel w hw).toBulkGraph)
          ≤ cutWeight (pairModel w hw).toBulkGraph (single 0) := Finset.inf'_le _ hmem
        _ = w := hcw0
    · refine Finset.le_inf' _ _ (fun f hf => ?_)
      rw [hsep, Finset.mem_singleton] at hf
      subst hf
      exact le_of_eq hcw0.symm
  refine ⟨hthroat, ?_⟩
  rw [hthroat, mutualInfo, hent, hent, hent, hcw0, hcw1, hcwall]
  ring
