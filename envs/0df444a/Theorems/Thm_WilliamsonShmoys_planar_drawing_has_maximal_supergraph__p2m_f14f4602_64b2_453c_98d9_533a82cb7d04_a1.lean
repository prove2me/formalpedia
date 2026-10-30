-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:29.563195+00:00
-- url     : https://prove2.me/theorems/b95266d4-e515-4cba-bd9d-c9d06115dc07
-- title:
--   Every finite planar drawing has a maximal planar supergraph on the same vertices
-- statement:
--   Any finite graph with a drawing witness has a supergraph on the same vertices that also has a drawing witness and admits no strictly larger planar supergraph on those vertices. The child does not require |V| ≥ 3: maximality exists by finiteness of the set of simple graphs on V. This removes the maximal-extension existence step from the parent. A proof route is to consider all supergraphs of K that have a drawing witness and choose one with maximal edge-set cardinality; a strictly larger supergraph would contradict that choice. The remaining obligation is to formalize the finite maximization and subgraph/cardinality argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_f14f4602_64b2_453c_98d9_533a82cb7d04_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
