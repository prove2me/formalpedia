-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulatedSphereFaceData_side_count
-- name    : WilliamsonShmoys.triangulatedSphereFaceData_side_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:05:56.876323+00:00
-- url     : https://prove2.me/theorems/4b93b83f-f03f-4d08-b849-bcbbfb7cf553
-- title:
--   Count triangular face sides by graph edges
-- statement:
--   For triangular sphere face data, the total number of face-side occurrences is three times the number of faces and equals twice the number of graph edges, since each graph edge occurs exactly twice among the sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.triangulatedSphereFaceData_side_count
    {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    (data : WilliamsonShmoys.TriangulatedSphereFaceData K)
    [Fintype data.Face] :
    3 * (Fintype.card data.Face : Int) = 2 * (K.edgeSet.ncard : Int) := by sorry
