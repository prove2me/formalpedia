-- Prove2me | Theorems.Thm_WilliamsonShmoys_nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- name    : WilliamsonShmoys.nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:57.013201+00:00
-- url     : https://prove2.me/theorems/64181819-5dbf-45ad-9421-ecf2885eb354
-- title:
--   Summing component edge bounds over natural sizes
-- statement:
--   For finitely many natural-number component sizes and contributions satisfying the stated piecewise bounds, if the total size is at least three, then the total contribution is at most three times the total size minus six. The component cases retain the exact small-size allowances; a proof can sum the per-component deficits from `3 * s i` and show that their total is at least six. This isolates the arithmetic obligation from graph edge counting, which remains handled in the parent by `hedges`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.nat_sum_component_edge_bounds__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
    {ι : Type} [Fintype ι] (s a : ι → ℕ)
    (hsize : 3 ≤ ∑ i : ι, s i)
    (hlocal : ∀ i,
      if 3 ≤ s i then a i ≤ 3 * s i - 6
      else if 2 ≤ s i then a i ≤ 1
      else a i = 0) :
    (∑ i : ι, a i) ≤ 3 * (∑ i : ι, s i) - 6 := by sorry
