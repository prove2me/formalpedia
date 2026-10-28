-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_incidence_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_incidence_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:24:44.070775+00:00
-- url     : https://prove2.me/theorems/9293bfe6-bf33-4fc6-92bb-50cfb472a42e
-- title:
--   Face-edge incidence bound for a planar drawing
-- statement:
--   For a connected simple graph with the specified drawing and at least three vertices, every natural face count satisfying Euler’s equation obeys the face-edge incidence inequality. This removes the incidence portion of the parent. A proof can count two edge-sides per edge and establish that every facial boundary walk has length at least three, then combine that count with the supplied Euler equation. The hypotheses retain the connectedness, simplicity, and minimum vertex count needed to handle bridges and exclude short exceptional boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_incidence_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f ≤ 2 * L.edgeSet.ncard := by sorry
