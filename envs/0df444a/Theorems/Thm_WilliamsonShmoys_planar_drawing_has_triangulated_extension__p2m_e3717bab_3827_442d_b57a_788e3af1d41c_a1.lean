-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:41:55.987109+00:00
-- url     : https://prove2.me/theorems/67db8130-6ce9-48ac-b689-e2c8fddc3a6e
-- title:
--   Triangulated extension of a drawable graph
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_e3717bab_3827_442d_b57a_788e3af1d41c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
