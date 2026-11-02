-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1
-- name    : WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:49.041647+00:00
-- url     : https://prove2.me/theorems/4ae5c893-7e52-474c-915d-3ed4ab7c0e94
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   On a finite ordered vertex type, any graph satisfying a property has a property-satisfying supergraph that is inclusion-maximal among such supergraphs; its edge count is at least that of the starting graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_finite_maximal_drawable_extension__p2m_646dfb24_703c_493f_8075_444718d53d7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      (∀ G : SimpleGraph V, H ≤ G → P G → G ≤ H) ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
