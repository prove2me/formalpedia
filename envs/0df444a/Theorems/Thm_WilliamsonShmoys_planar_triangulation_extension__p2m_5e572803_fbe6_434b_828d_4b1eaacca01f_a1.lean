-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:48.78055+00:00
-- url     : https://prove2.me/theorems/2e946047-ffd1-46bc-894e-b6ef062eed83
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is a subgraph of a planar graph on the same vertices whose edge count is 3|V| − 6. This is the standard triangulation extension step; it removes the topological graph argument from the parent, leaving only maximality and equality rewriting there.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
