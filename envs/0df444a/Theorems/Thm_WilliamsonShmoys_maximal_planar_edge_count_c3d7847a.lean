-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_c3d7847a
-- name    : WilliamsonShmoys.maximal_planar_edge_count_c3d7847a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:39:19.962915+00:00
-- url     : https://prove2.me/theorems/cf53a3e0-742b-4c75-857e-72882cae715b
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that has no drawable strict supergraph has exactly three times the number of vertices minus six edges. The proof proceeds from maximality to a triangulated plane embedding, then counts vertices, edges, and faces using Euler's formula. The lower bound on the number of vertices is preserved because the formula need not hold for maximal planar graphs on fewer vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_c3d7847a
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K.edgeSet = J.edgeSet) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
