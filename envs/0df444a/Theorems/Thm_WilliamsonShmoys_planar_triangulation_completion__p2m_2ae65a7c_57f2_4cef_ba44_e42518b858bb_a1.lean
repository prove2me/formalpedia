-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:55.472723+00:00
-- url     : https://prove2.me/theorems/9e7a2e08-df96-4db8-828f-8ffe40cd0bda
-- title:
--   Completion of a drawable graph to a triangulation
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel T.Adj := dT
       W.edgeFinset ⊆ T.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       T.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
