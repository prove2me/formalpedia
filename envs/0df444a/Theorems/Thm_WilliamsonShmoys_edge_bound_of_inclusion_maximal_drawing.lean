-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_inclusion_maximal_drawing
-- name    : WilliamsonShmoys.edge_bound_of_inclusion_maximal_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:38:34.702033+00:00
-- url     : https://prove2.me/theorems/b91e3086-4225-4a64-a8b2-041818632bd0
-- title:
--   Edge bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal graph admitting the supplied crossing-free arc drawing has at least 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_inclusion_maximal_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
