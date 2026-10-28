-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_euler_formula
-- name    : WilliamsonShmoys.planar_connected_euler_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:18:47.511307+00:00
-- url     : https://prove2.me/theorems/5d6b35c9-7d5a-4e47-ba09-8b462f7aebea
-- title:
--   Euler formula for a connected finite plane graph
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_euler_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
