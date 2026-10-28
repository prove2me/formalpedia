-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected_for_euler_equations
-- name    : WilliamsonShmoys.maximal_drawable_connected_for_euler_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:22:03.996766+00:00
-- url     : https://prove2.me/theorems/5d32aa93-15cd-4330-8a58-7e1c874b83e8
-- title:
--   Maximal drawable graphs are connected for Euler counting
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_connected_for_euler_equations {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L = M) (hCard : 3 ≤ Fintype.card V) : L.Connected := by sorry
