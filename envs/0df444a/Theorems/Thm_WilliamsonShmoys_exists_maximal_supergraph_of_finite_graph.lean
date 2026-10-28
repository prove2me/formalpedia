-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_graph
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:52:29.630287+00:00
-- url     : https://prove2.me/theorems/8efe41fc-e123-4df9-b7af-7475bb9ec325
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For any property of simple graphs on a finite vertex type, if the property holds for G, then G has a supergraph satisfying the property that is maximal among such supergraphs; its edge count is at least that of G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
