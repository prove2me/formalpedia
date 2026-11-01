-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:10:06.756198+00:00
-- url     : https://prove2.me/theorems/ac3a3788-6a22-4a7a-9025-c2d661b5eddf
-- title:
--   A sparse planar drawing admits a strict planar edge extension
-- statement:
--   For a finite linearly ordered vertex type of size at least three, any graph with a crossing-free drawing and fewer than 3|V|−6 edges has a crossing-free supergraph on the same vertices with strictly more edges. The parent applies this to U and contradicts edge maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_of_small_card__p2m_6f7b33c7_a7c9_44db_bbb3_dcbcd538e90d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V)
    (hsmall : (letI : DecidableRel U.Adj := dU
      U.edgeFinset.card + 6 < 3 * Fintype.card V)) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) ∧
      ¬ (letI : DecidableRel U.Adj := dU
         letI : DecidableRel W.Adj := dW
         W.edgeFinset ⊆ U.edgeFinset) := by sorry
