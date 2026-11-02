-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:12:37.432734+00:00
-- url     : https://prove2.me/theorems/9948da09-8892-4f55-9a10-a3a5f578a96b
-- title:
--   An inclusion-maximal drawable graph has planar density
-- statement:
--   An inclusion-maximal graph with a drawing of the specified kind has at least `3|V| - 6` edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_dense__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
