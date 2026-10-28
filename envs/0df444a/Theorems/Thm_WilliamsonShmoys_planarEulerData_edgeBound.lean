-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEulerData_edgeBound
-- name    : WilliamsonShmoys.planarEulerData_edgeBound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:37:45.337992+00:00
-- url     : https://prove2.me/theorems/d0954f24-d409-41f1-ad82-4663af583c0d
-- title:
--   Edge bound from plane-map Euler data
-- statement:
--   For a graph with finite face-count data satisfying Euler’s formula and the face-boundary incidence inequality, at least three vertices imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarEulerData

theorem WilliamsonShmoys.planarEulerData_edgeBound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (data : WilliamsonShmoys.PlanarEulerData G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
