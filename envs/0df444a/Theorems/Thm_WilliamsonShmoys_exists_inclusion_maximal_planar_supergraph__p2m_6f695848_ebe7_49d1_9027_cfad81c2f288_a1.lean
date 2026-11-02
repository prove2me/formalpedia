-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:34.116038+00:00
-- url     : https://prove2.me/theorems/d650c46c-07cd-4c1b-ae64-d3c9997f4f25
-- title:
--   An inclusion-maximal drawable supergraph exists
-- statement:
--   Among the drawable supergraphs of N on the same finite vertex type, there is one that has no strictly larger drawable supergraph. The proof is finite maximization over edge sets; n≥3 is retained to match the parent and the edge-count result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by sorry
