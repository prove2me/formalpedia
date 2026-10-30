-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_and_incidence
-- name    : WilliamsonShmoys.maximal_planar_euler_and_incidence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:48:05.745818+00:00
-- url     : https://prove2.me/theorems/ac69e49c-7b63-4757-a149-d1ffff7b54d9
-- title:
--   Euler and face incidence for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying both Euler’s vertex-edge-face equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_and_incidence {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = J.edgeSet.ncard + 2 ∧ 3 * f = 2 * J.edgeSet.ncard := by sorry
