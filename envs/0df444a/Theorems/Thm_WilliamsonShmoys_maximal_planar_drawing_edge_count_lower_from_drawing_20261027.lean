-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_from_drawing_20261027
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_from_drawing_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:34:45.514653+00:00
-- url     : https://prove2.me/theorems/5ab0a9dc-5891-4a58-a10c-00f92a2ee40d
-- title:
--   Maximal planar drawing edge count lower bound from drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V|−6 edges. For |V| = 3, maximality forces all three edges, consistent with the bound. This lemma removes the maximality-to-density step from the target. A proof route is to augment the drawing to a triangulation without adding vertices; maximality then forces the augmented graph to equal G, and Euler’s formula gives its edge count. The remaining work is establishing and counting that augmentation for the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_from_drawing_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      G ≤ K → HasPlanarDrawingOn K → K ≤ G) :
    3 * (Fintype.card V : Int) - 6 ≤ (G.edgeSet.ncard : Int) := by sorry
