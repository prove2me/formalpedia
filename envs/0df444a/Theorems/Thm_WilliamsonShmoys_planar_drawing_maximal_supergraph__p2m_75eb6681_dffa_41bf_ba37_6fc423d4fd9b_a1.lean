-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:07.46719+00:00
-- url     : https://prove2.me/theorems/ec2412ad-17a6-418f-a499-5de65dee72a0
-- title:
--   Maximum drawable supergraph exists
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex set whose edge count is at least that of every other drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ N' : SimpleGraph V, M ≤ N' → HasPlanarDrawingOn N' →
        (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj
         N'.edgeFinset.card) ≤
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj
         N.edgeFinset.card) := by sorry
