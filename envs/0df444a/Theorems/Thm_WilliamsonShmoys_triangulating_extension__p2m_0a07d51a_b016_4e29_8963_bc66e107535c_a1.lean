-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1
-- name    : WilliamsonShmoys.triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:36:51.730307+00:00
-- url     : https://prove2.me/theorems/c20796cc-c576-4992-b291-9784ec70fc6e
-- title:
--   Drawable graphs extend to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
