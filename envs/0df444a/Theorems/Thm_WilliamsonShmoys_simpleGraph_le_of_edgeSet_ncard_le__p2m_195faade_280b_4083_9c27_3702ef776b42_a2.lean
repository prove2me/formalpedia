-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- name    : WilliamsonShmoys.simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:43.673245+00:00
-- url     : https://prove2.me/theorems/2b605497-a94c-49bc-bb54-a5d4df08c566
-- title:
--   Reverse graph inclusion from edge-count bounds
-- statement:
--   For simple graphs on a finite vertex type, if `R` is a subgraph of `S` and `S` has no more edges than `R`, then `S` is also a subgraph of `R`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (R S : SimpleGraph V) (hRS : R ≤ S)
    (hcard : S.edgeSet.ncard ≤ R.edgeSet.ncard) : S ≤ R := by
  sorry
