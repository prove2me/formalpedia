-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data
-- name    : WilliamsonShmoys.planar_drawing_euler_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:45:46.533986+00:00
-- url     : https://prove2.me/theorems/e114997d-5331-4883-8748-cff79fbe3133
-- title:
--   Extract Euler face data from a planar drawing
-- statement:
--   A crossing-free drawing of a connected simple graph with at least three vertices yields finite face data satisfying Euler’s formula, with each face boundary having length at least three and the total boundary length equal to twice the edge count. Bridges contribute twice to boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarEulerData
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_data {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) : Nonempty (PlanarEulerData G) := by sorry
