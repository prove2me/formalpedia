-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- name    : WilliamsonShmoys.euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:39.270138+00:00
-- url     : https://prove2.me/theorems/2542087f-d606-42ce-9f15-ed8697863b40
-- title:
--   Euler face count from a spanning tree in a planar drawing
-- statement:
--   For a finite graph with a crossing-free drawing, if it contains a connected spanning subgraph with one fewer edge than vertices, then it has a natural-number face count satisfying Euler's relation. This isolates the planar face-separation argument after the spanning tree has been supplied.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_from_spanning_tree__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H T : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hsub : T ≤ H)
    (hTconnected : T.Connected)
    (hTcard : T.edgeSet.ncard + 1 = Fintype.card V) :
    ∃ F : ℕ, Fintype.card V + F = H.edgeSet.ncard + 2 := by sorry
