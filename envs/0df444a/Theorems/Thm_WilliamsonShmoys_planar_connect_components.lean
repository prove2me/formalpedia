-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connect_components
-- name    : WilliamsonShmoys.planar_connect_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:57:21.936984+00:00
-- url     : https://prove2.me/theorems/3b4349cc-c4e3-44db-91fc-0afaa8bc9525
-- title:
--   Connect components without losing planarity or existing edges
-- statement:
--   A finite graph with a crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing, retaining every original edge and not decreasing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connect_components {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
