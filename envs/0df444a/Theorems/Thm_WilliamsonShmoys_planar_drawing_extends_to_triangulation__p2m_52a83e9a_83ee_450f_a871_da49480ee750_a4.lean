-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_52a83e9a_83ee_450f_a871_da49480ee750_a4
-- name    : WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_52a83e9a_83ee_450f_a871_da49480ee750_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:00:35.076539+00:00
-- url     : https://prove2.me/theorems/a2b32b85-3e62-4f8d-ac46-eae49e28b6fd
-- title:
--   A finite planar drawing extends to a triangulation
-- statement:
--   Every crossing-free drawing of a finite simple graph on at least three vertices extends, without adding vertices, to a crossing-free drawing whose graph has exactly $3|V|-6$ edges. This packages the planar augmentation and edge-count argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_52a83e9a_83ee_450f_a871_da49480ee750_a4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
