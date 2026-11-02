-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:49.130138+00:00
-- url     : https://prove2.me/theorems/715ac197-39c1-4c2e-9422-f143ea2fc18b
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every graph with a drawing on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal under inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V), ∃ (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
          HasPlanarDrawingOn K → H ≤ K → K ≤ H := by
  sorry
