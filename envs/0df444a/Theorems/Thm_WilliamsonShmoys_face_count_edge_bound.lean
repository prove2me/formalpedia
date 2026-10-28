-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_edge_bound
-- name    : WilliamsonShmoys.face_count_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:33:44.261951+00:00
-- url     : https://prove2.me/theorems/d100714a-48c1-4ec7-8c54-587a7271e5d0
-- title:
--   Derive the simple planar edge bound from face counts
-- statement:
--   Euler’s equation and the aggregate face-incidence inequality imply the edge bound by linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.face_count_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (heuler : K.edgeSet.ncard + 2 = Fintype.card V + f)
    (hfaces : 3 * f ≤ 2 * K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
