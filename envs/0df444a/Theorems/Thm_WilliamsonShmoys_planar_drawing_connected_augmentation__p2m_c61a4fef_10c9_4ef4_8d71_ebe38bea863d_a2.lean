-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:25.793478+00:00
-- url     : https://prove2.me/theorems/b19e8695-c9ea-46cf-beea-17c06dbec4b1
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   A finite drawn graph on at least three vertices can be extended, without changing its vertices, to a connected graph with a crossing-free drawing that contains all original edges. The cardinality assumption ensures that the connectedness predicate is meaningful even if the original graph has isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
