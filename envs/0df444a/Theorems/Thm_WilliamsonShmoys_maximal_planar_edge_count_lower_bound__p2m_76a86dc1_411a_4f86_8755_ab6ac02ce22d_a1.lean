-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:38.005135+00:00
-- url     : https://prove2.me/theorems/91c62409-832a-420e-9e29-0b556e5e78fe
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that admits no strict drawable supergraph on the same vertex set has at least 3|V|−6 edges. One proof route extends the drawing to a triangulation on the same vertices, uses maximality to identify the extension with T, and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by sorry
