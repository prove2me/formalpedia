-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:38.956448+00:00
-- url     : https://prove2.me/theorems/d1eb2181-eb8a-4716-8ab1-795e5105cb72
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal graph on at least three vertices with a drawing as defined in the supplied module has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hMax : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → H ≤ G → G ≤ H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
