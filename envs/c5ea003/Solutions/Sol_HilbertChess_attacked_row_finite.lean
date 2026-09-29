-- Prove2me | solution 1 for HilbertChess.attacked_row_finite
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:35.056196+00:00
-- url     : https://prove2.me/submissions/db67ba7c-59bb-4be5-8922-f8460c5819cc

import Mathlib
import Definitions.Def_Geometry_HilbertChessLines

open HilbertChess

theorem solution (S : List Line) (k : ℤ)
    (hk : ∀ L ∈ S, L.a = 0 → ¬ L.covers (0, k)) :
    {x : ℤ | attacked S (x, k)}.Finite := by
  classical
  have hsub : {x : ℤ | attacked S (x, k)} ⊆
      ⋃ L ∈ S.toFinset, {x : ℤ | L.covers (x, k)} := by
    intro x hx
    rcases hx with ⟨L, hL, hcov⟩
    exact Set.mem_biUnion (List.mem_toFinset.mpr hL) hcov
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (S.toFinset.finite_toSet) fun L hL => ?_
  by_cases ha : L.a = 0
  · have hLmem : L ∈ S := List.mem_toFinset.mp hL
    have hn : ¬ L.covers (0, k) := hk L hLmem ha
    have hempty : {x : ℤ | L.covers (x, k)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Line.covers]
      intro hcov
      have : L.b * k = L.c := by simpa [ha, zero_mul, zero_add] using hcov
      exact hn (by simp [Line.covers, ha, this])
    simpa [hempty] using Set.finite_empty
  · refine (Set.finite_singleton ((L.c - L.b * k) / L.a)).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Line.covers] at hx
    have hx' : L.a * x = L.c - L.b * k := by
      -- from a*x + b*k = c
      linarith
    have hxeq : x = (L.c - L.b * k) / L.a :=
      Int.eq_ediv_of_mul_eq_right ha (by linarith)
    exact hxeq ▸ Set.mem_singleton _
