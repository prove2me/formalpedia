-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_a_missing_edge
-- name    : WilliamsonShmoys.planar_drawing_adds_a_missing_edge
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T09:15:35.078536+00:00
-- url     : https://prove2.me/theorems/ae3397b1-5a5b-4ac0-9733-dc2c1507aff9
-- title:
--   Add a missing edge between components of a planar drawing
-- statement:
--   For a finite disconnected graph with a drawing satisfying the given crossing-free arc conditions, there are vertices in distinct components whose single connecting edge can be added while preserving those drawing conditions. The edge graph in the statement makes the augmentation exact.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_adds_a_missing_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ P.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn
        (P ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by
  sorry
