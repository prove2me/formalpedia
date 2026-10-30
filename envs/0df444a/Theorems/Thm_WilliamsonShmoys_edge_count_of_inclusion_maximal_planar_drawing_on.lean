-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_drawing_on
-- name    : WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:15:34.783061+00:00
-- url     : https://prove2.me/theorems/277e8683-c36a-4ff8-9d7f-ab79875bd918
-- title:
--   Count the edges of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges. This removes the planar edge-count argument from the parent. A proof route is to show that maximality forces all faces to be triangles, then combine Euler’s formula with face-edge incidence counting. The hypothesis |V| ≥ 3 is preserved because the formula does not apply to maximal planar graphs on fewer vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing_on
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
