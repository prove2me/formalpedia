-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_b94a5187
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_b94a5187
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:00:10.445224+00:00
-- url     : https://prove2.me/theorems/54ea6f37-9844-461c-8824-1262dec34216
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on those vertices has at most `3|V| - 6` edges. The proof route is to establish triangulation from maximality and apply Euler's formula with face-degree counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_b94a5187
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
