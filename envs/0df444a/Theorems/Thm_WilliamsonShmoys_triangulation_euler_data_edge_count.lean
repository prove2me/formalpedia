-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_euler_data_edge_count
-- name    : WilliamsonShmoys.triangulation_euler_data_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:26:44.741446+00:00
-- url     : https://prove2.me/theorems/e2f7f581-20b1-4941-a342-8361ae2b945a
-- title:
--   Count edges from triangular face data
-- statement:
--   Count the finite face-side occurrences by faces and by graph edges. There are three sides per face and exactly two occurrences per graph edge; side adjacency ensures every occurrence is a graph edge. Hence 3F = 2E, and the data’s Euler equation V − E + F = 2 gives E = 3V − 6 by integer algebra. The explicit `[DecidableEq V]` supports the occurrence predicate and is available from the parent’s `[LinearOrder V]`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_euler_data_edge_count
    {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    (data : WilliamsonShmoys.TriangulatedSphereFaceData K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
