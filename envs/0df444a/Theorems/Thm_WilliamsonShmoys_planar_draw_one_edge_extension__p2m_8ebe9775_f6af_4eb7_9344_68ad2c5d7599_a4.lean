-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_draw_one_edge_extension__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- name    : WilliamsonShmoys.planar_draw_one_edge_extension__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:58.118842+00:00
-- url     : https://prove2.me/theorems/428844a2-eb50-4679-aa28-45fa77ab4049
-- title:
--   Draw the one-edge extension between unreachable vertices
-- statement:
--   A drawing of a finite graph can be replaced by a drawing of its extension with the edge between two distinct unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_draw_one_edge_extension__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hN : HasPlanarDrawingOn N)
    (u v : V) (huv : u ≠ v) (hUnreachable : ¬ N.Reachable u v) :
    HasPlanarDrawingOn
      (N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)) := by sorry
