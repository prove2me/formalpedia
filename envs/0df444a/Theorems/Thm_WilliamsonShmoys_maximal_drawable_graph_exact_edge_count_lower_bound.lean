-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:17:31.313562+00:00
-- url     : https://prove2.me/theorems/270155f1-1a76-47ff-bf00-e4e6ed3e833b
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A graph with a drawing satisfying `HasPlanarDrawingOn`, at least three vertices, and no drawable strict edge-set supergraph on the same vertex type has at least `3|V| − 6` edges, expressed without truncated subtraction. This removes the maximality and augmentation argument from the parent. A proof route is to show maximality forces a triangulation on the given vertices, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → False)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
