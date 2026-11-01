-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:21.748359+00:00
-- url     : https://prove2.me/theorems/bcf9fc22-a10c-472d-8ae6-0fdb1da6c723
-- title:
--   Exact edge-count planar completion
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_368c0d6c_27a0_4bf2_9016_cc54673fe776_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
