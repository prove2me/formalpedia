-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:10.424387+00:00
-- url     : https://prove2.me/theorems/2cf5c394-8fe3-4b96-8033-bf5d04367b46
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Any finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
