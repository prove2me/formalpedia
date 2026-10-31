-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2
-- name    : WilliamsonShmoys.planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:36.124886+00:00
-- url     : https://prove2.me/theorems/3b4f1a59-3c0d-4d63-aeba-130ad9fe1fcf
-- title:
--   Drawable graphs extend to a spanning triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable spanning supergraph whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
