-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1
-- name    : WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:32.49417+00:00
-- url     : https://prove2.me/theorems/1ca97e7b-39c1-4582-9f62-016443dae810
-- title:
--   Maximal planar augmentation on a fixed vertex set
-- statement:
--   Every connected drawable simple graph on at least three vertices has a drawable supergraph on the same vertices that is maximal under drawable edge extension and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (instH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      (∀ (G' : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G' →
        (∀ u v, H.Adj u v → G'.Adj u v) →
        (∀ u v, G'.Adj u v → H.Adj u v)) ∧
      (letI : DecidableRel H.Adj := instH; K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
