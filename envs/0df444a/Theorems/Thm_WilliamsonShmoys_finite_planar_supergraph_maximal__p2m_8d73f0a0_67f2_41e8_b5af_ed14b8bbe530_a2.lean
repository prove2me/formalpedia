-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:15.519929+00:00
-- url     : https://prove2.me/theorems/888eaaab-3757-4ebd-aa3e-d8ad95a4c45e
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_maximal__p2m_8d73f0a0_67f2_41e8_b5af_ed14b8bbe530_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
