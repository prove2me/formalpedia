-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- name    : WilliamsonShmoys.maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:28.473472+00:00
-- url     : https://prove2.me/theorems/30f04ba5-7c4d-43f6-bbf4-fbaceb7763c4
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A graph maximal under inclusion among drawable graphs on the same finite ordered vertex type, with at least three vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
