-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- name    : WilliamsonShmoys.planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:34.258852+00:00
-- url     : https://prove2.me/theorems/13106ccf-4a77-4116-9776-5cbeac94b552
-- title:
--   Construct finite face data from the two edge bounds
-- statement:
--   Given the connected-graph lower edge bound and planar upper edge bound, construct the abstract `PlanarMapData` record. This removes the numerical bookkeeping from the parent and does not assert that the degree list is realized by geometric face boundaries. Set the face count to `E - n + 2`, give each index degree three, and add the surplus `2E - 3F` to one index; the hypotheses ensure `F > 0`, the Euler equation, nonnegative surplus, and total degree `2E`. This is a direct finite arithmetic and `Finset.sum` proof. The condition `n ≥ 3` and both edge inequalities are retained explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

theorem WilliamsonShmoys.planarMapData_of_edge_bounds__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : 3 <= Fintype.card V)
    (hlow : Fintype.card V <= J.edgeFinset.card + 1)
    (hupp : J.edgeFinset.card + 6 <= 3 * Fintype.card V) :
    Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) := by sorry
