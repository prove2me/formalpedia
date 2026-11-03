-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:13.419874+00:00
-- url     : https://prove2.me/theorems/5372b848-7d0c-4e54-bcd1-c004f9c1519b
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A finite simple graph that is maximal among drawable supergraphs on the same vertex set, and has at least three vertices, has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; 3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by sorry
