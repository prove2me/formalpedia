-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:16.806726+00:00
-- url     : https://prove2.me/theorems/cfcb8007-1ff9-4f3a-9061-c47c5589ef6f
-- title:
--   Triangulating extension of a finite planar graph
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       3 * Fintype.card V = M.edgeFinset.card + 6) := by sorry
