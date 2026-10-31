-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:02.135604+00:00
-- url     : https://prove2.me/theorems/eaa2f707-0afb-4e00-8b05-dfb2bc697223
-- title:
--   Lower bound for maximal planar graphs
-- statement:
--   A graph maximal under planar edge-preserving extension, with at least three vertices, has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) : 3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
