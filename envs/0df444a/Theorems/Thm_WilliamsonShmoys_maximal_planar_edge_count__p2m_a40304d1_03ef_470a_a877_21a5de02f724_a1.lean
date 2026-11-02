-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:35.163356+00:00
-- url     : https://prove2.me/theorems/2629fd8d-6fc9-4c07-8b09-9c33cf4a1063
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal planar simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) [DecidableRel H.Adj] (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, (∀ u v, H.Adj u v → K.Adj u v) → HasPlanarDrawingOn K → ∀ u v, K.Adj u v → H.Adj u v) : H.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
