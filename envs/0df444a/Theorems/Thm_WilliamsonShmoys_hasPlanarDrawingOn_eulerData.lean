-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_eulerData
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_eulerData
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:31:47.633875+00:00
-- url     : https://prove2.me/theorems/ee668d5a-cece-412b-b4ca-fa597fcc222e
-- title:
--   Plane-map Euler data from a connected crossing-free drawing
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing admits finite face-count data satisfying Euler’s formula and the face-boundary incidence inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarEulerData

theorem WilliamsonShmoys.hasPlanarDrawingOn_eulerData
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    Nonempty (WilliamsonShmoys.PlanarEulerData G) := by sorry
