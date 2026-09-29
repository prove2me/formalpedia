-- Prove2me | solution 1 for GilbertLattice.adj_horiz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:30:09.958808+00:00
-- url     : https://prove2.me/submissions/02d8c04b-d355-4c99-ba4f-2cbc09bb0108

-- Sol generated from Shared/GilbertLatticeConnectivity.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Theorems.Thm_GilbertLattice_adj_of_sqdist_lt

/-!
# Full connectivity of the conditioned Gilbert model for large radii

The third critical radius of the model is

`R_full = inf {R : for every placement of the points, all points are connected}`.

Two points sitting in two cells sharing an edge are at distance at most
`√(2² + 1²) = √5`, whatever the placement.  Consequently, as soon as `R > √5`, every
placement produces a graph containing the whole nearest-neighbour grid graph of `ℤ²`,
which is connected.  This gives `R_full ≤ √5`; the companion file
`GilbertLatticeConstructions.lean` provides the lower bound `R_full ≥ √17 / 2`.
-/

open GilbertLattice

variable {R : ℝ} (C : Config)

lemma sq_five_lt (hR : Real.sqrt 5 < R) : 5 < R ^ 2 ∧ 0 < R := by
  have hs : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hR0 : 0 < R := lt_of_le_of_lt hs hR
  refine ⟨?_, hR0⟩
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith






open GilbertLattice in
lemma solution(hR : Real.sqrt 5 < R) (i j : ℤ) :
    (gilbert R C).Adj (i, j) (i + 1, j) := by
  obtain ⟨hR2, hR0⟩ := sq_five_lt hR
  refine adj_of_sqdist_lt hR0 (by intro h; rw [Prod.ext_iff] at h; omega) ?_
  have a1 := C.off_nonneg_fst (i, j)
  have a2 := C.off_le_one_fst (i, j)
  have a3 := C.off_nonneg_fst (i + 1, j)
  have a4 := C.off_le_one_fst (i + 1, j)
  have b1 := C.off_nonneg_snd (i, j)
  have b2 := C.off_le_one_snd (i, j)
  have b3 := C.off_nonneg_snd (i + 1, j)
  have b4 := C.off_le_one_snd (i + 1, j)
  unfold sqdist px py
  push_cast
  nlinarith [a1, a2, a3, a4, b1, b2, b3, b4]
