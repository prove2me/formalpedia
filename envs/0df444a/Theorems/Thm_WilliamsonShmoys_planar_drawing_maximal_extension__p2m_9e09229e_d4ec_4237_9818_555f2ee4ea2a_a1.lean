-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:59.971582+00:00
-- url     : https://prove2.me/theorems/8526028d-6503-4baf-b95b-7d2634d3c3de
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph on those vertices. This also covers disconnected graphs and cut vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ K : SimpleGraph V, L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) := by sorry
