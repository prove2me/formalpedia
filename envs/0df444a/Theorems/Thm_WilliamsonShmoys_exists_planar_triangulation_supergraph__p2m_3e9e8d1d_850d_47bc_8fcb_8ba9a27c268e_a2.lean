-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_3e9e8d1d_850d_47bc_8fcb_8ba9a27c268e_a2
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_3e9e8d1d_850d_47bc_8fcb_8ba9a27c268e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:00.723923+00:00
-- url     : https://prove2.me/theorems/1d01f0c3-2d78-4cc0-a2e5-f8506e5ee0a0
-- title:
--   Planar supergraph with the triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This supplies the maximal planar edge count used by the parent reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_3e9e8d1d_850d_47bc_8fcb_8ba9a27c268e_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧ R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
