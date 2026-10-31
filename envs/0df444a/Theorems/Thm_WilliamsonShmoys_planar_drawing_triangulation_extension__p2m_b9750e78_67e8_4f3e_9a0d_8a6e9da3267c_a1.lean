-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:27.229526+00:00
-- url     : https://prove2.me/theorems/cb71297e-2af2-47af-8fd1-d009bcc4ef4e
-- title:
--   Triangulated planar supergraph extension
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing can be extended, on the same vertex set, to a crossing-free graph with exactly 3(|V|−2) edges, while preserving all original edges. The monotonicity clause records the edge-count consequence needed by the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * (Fintype.card V - 2) := by sorry
