-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_component_count
-- name    : WilliamsonShmoys.planar_drawing_euler_component_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:54:54.19918+00:00
-- url     : https://prove2.me/theorems/7f608e52-d030-4f39-85a9-0fadd8740c63
-- title:
--   Euler relation with the exact connected-component count
-- statement:
--   For a finite graph with at least three vertices and a crossing-free drawing, the number of faces can be chosen so Euler’s relation uses the graph’s actual connected-component count, `Nat.card L.ConnectedComponent`, which is positive. This strengthens the existing existential Euler relation by fixing the meaning of its component count. A proof can count faces via the drawing’s planar embedding and track components explicitly, or adapt the spanning connected extension proof while accounting for the components joined.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_component_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + Nat.card L.ConnectedComponent + 1 ∧
      1 ≤ Nat.card L.ConnectedComponent := by sorry
