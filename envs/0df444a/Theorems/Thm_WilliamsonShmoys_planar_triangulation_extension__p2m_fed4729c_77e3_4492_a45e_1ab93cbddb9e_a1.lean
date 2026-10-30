-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:13.661999+00:00
-- url     : https://prove2.me/theorems/237d0a74-b3e5-4601-9e6d-1aac4d25b642
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing, there is a planar supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_fed4729c_77e3_4492_a45e_1ab93cbddb9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
