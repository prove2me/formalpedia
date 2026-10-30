-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:56.934323+00:00
-- url     : https://prove2.me/theorems/4389f167-4c7c-4d6b-b9d1-6f89e764ff11
-- title:
--   Edge bound for an inclusion-maximal drawn graph
-- statement:
--   An inclusion-maximal simple graph admitting the supplied crossing-free drawing has at most 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
