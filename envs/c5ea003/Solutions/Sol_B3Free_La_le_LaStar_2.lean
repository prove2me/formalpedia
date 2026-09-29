-- Prove2me | solution 2 for B3Free.La_le_LaStar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:22:45.253463+00:00
-- url     : https://prove2.me/submissions/e770c460-8c04-4317-983f-ef1f65498a83

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] (P : Type*) [Preorder P] :
    La α P ≤ LaStar α P := by
  classical
  unfold La LaStar
  refine Finset.sup_mono ?_
  intro F hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
  rintro ⟨ι, hcopy, hmem⟩
  exact hF ⟨ι, ⟨hcopy.1, fun p q hpq => (hcopy.2 p q).mpr hpq⟩, hmem⟩
