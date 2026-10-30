-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_64cb9f36
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_64cb9f36
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:39:19.395306+00:00
-- url     : https://prove2.me/theorems/7287af43-e5e2-47cd-87fe-774f35508d27
-- title:
--   An edge-maximal planar drawing has the triangulation edge count
-- statement:
--   A simple graph on at least three vertices whose planar drawing admits no strictly larger planar supergraph has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_64cb9f36
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hPmax : ∀ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn Q) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
