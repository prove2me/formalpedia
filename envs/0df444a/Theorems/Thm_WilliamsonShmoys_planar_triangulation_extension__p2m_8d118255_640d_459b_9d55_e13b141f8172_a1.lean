-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:28:47.009257+00:00
-- url     : https://prove2.me/theorems/9e09229e-d4ec-4237-9818-555f2ee4ea2a
-- title:
--   Extend a planar drawing to a triangulation on the same vertices
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, without adding vertices, to a drawable graph with exactly 3|V|−6 edges. The statement covers disconnected graphs and drawings with cut vertices; these cases must be handled in the extension argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
