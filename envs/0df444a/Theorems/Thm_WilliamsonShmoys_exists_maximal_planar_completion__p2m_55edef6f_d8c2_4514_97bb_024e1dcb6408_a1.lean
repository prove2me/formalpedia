-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_completion__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:15.88896+00:00
-- url     : https://prove2.me/theorems/55f6d7b4-4de2-400e-aa1d-9225bf419203
-- title:
--   Finite maximal drawable completion
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs of the original graph. The child removes the finite maximization and preservation-of-drawing construction from the parent. Prove it by maximizing the edge count among the finite set of drawable supergraphs; any proper supergraph has strictly more edges. The drawing predicate is inherited directly for the selected maximizer. This does not establish the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_completion__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) := by sorry
