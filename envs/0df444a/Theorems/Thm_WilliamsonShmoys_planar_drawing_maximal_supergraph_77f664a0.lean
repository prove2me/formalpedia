-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_77f664a0
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_77f664a0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:44:51.826888+00:00
-- url     : https://prove2.me/theorems/31453246-080d-4b85-8aed-34708c7592ba
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every finite drawable simple graph with at least three vertices has a drawable edge-maximal supergraph on the same vertex set. This removes the finite maximization step from the parent. Independently, maximize edge-set cardinality among drawable supergraphs; the family is finite and contains the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_77f664a0
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by sorry
