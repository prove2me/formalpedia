-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:08.748417+00:00
-- url     : https://prove2.me/theorems/92efd15a-1c37-4034-81a1-98dbd8d1208a
-- title:
--   Planar drawing has a maximal triangulated completion
-- statement:
--   Every graph with a planar drawing on at least three fixed vertices has a planar supergraph on those same vertices with exactly 3|V|−6 edges. The child captures the triangulated-completion theorem; the parent’s maximality hypothesis then forces the original graph to equal that completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
