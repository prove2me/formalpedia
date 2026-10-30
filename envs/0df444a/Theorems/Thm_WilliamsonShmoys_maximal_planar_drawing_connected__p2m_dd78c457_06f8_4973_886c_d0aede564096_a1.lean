-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:40:53.306661+00:00
-- url     : https://prove2.me/theorems/b968de7a-bb4e-4b2a-a58b-cf3030ff5cd1
-- title:
--   Maximal planar drawing implies connectedness
-- statement:
--   A graph on at least three vertices with a planar drawing that is maximal under planar edge additions is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.Connected := by sorry
