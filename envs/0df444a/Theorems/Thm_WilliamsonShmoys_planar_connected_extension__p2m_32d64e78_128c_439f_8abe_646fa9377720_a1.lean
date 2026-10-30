-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- name    : WilliamsonShmoys.planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:23.647213+00:00
-- url     : https://prove2.me/theorems/5b4ba625-e76a-490b-a06e-75a37c9ee7a0
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any graph on at least three vertices with the supplied crossing-free drawing has a connected supergraph on the same vertex set that still has such a drawing. The condition on the number of vertices avoids the empty and small-vertex connectedness boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
