-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_from_crossing_free_arcs_eae47bd5
-- name    : WilliamsonShmoys.euler_from_crossing_free_arcs_eae47bd5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:38:09.816834+00:00
-- url     : https://prove2.me/theorems/6352957b-91ea-4a29-85ed-b0ea02ef8bbf
-- title:
--   Euler formula from crossing-free arcs
-- statement:
--   For the supplied crossing-free arc drawing of a connected graph with at least three vertices, construct a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_from_crossing_free_arcs_eae47bd5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
