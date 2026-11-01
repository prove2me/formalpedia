-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:45.403442+00:00
-- url     : https://prove2.me/theorems/ef8dab25-617a-4455-968a-bd2c49e19056
-- title:
--   Maximal planar extension and edge count
-- statement:
--   Any finite simple graph on at least three ordered vertices with a crossing-free drawing is contained, on the same vertex set, in a drawn simple graph whose edge count is exactly 3|V|−6; the original edge count is no larger. This is the augmentation-and-Euler step needed by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      (∀ ⦃u v : V⦄, U.Adj u v → W.Adj u v) ∧
      HasPlanarDrawingOn W ∧
      (letI : DecidableRel W.Adj := dW
       W.edgeFinset.card + 6 = 3 * Fintype.card V) ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset.card ≤ W.edgeFinset.card) := by sorry
