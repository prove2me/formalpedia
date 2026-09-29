-- Prove2me | solution 1 for TropicalElimination.tropAdd_mem_tropVanishing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:16:22.449714+00:00
-- url     : https://prove2.me/submissions/45231d3d-bf3d-4fe8-83b7-7b605462a029

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination
open TropicalElimination in
theorem solution {E : Type*} (c : E → TT) {x y : E → TT} (hx : x ∈ tropVanishing c)
    (hy : y ∈ tropVanishing c) : tropAdd x y ∈ tropVanishing c := by
  intro i
  -- the minimum at `i` is attained by `x` or by `y`; reuse that vector's witness `j`
  rcases le_total (x i) (y i) with h | h
  · obtain ⟨j, hji, hj⟩ := hx i
    refine ⟨j, hji, ?_⟩
    simp only [tropAdd, min_eq_left h]
    calc c j + min (x j) (y j) ≤ c j + x j := add_le_add_right (min_le_left _ _) _
      _ ≤ c i + x i := hj
  · obtain ⟨j, hji, hj⟩ := hy i
    refine ⟨j, hji, ?_⟩
    simp only [tropAdd, min_eq_right h]
    calc c j + min (x j) (y j) ≤ c j + y j := add_le_add_right (min_le_right _ _) _
      _ ≤ c i + y i := hj
