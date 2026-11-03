-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1
-- name    : WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:00:53.684097+00:00
-- url     : https://prove2.me/theorems/aa8c3543-6a70-4578-ab0d-df04a85e5168
-- title:
--   Euler edge bound for the custom planar drawing predicate
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most three times its number of vertices minus six edges. The statement covers disconnected graphs and includes the three-vertex boundary case; it does not assume maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V) : ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
