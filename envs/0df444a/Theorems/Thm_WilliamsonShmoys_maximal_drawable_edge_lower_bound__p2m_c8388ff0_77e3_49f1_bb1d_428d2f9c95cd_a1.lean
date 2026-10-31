-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:03.663078+00:00
-- url     : https://prove2.me/theorems/c7679b9a-27a8-48b2-a15f-121d0cd77aa1
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3(|V|−2) edges. This isolates the planar topology and Euler-counting work. A proof route is to show maximality forces every face boundary in a planar embedding to be triangular, then count face-edge incidences and use Euler’s formula. For |V| = 3 the bound is 3, consistent with the triangle; the hypothesis must be retained for the Euler count and truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) (hmax : ∀ G : SimpleGraph V, H ≤ G → HasPlanarDrawingOn G → G = H) : 3 * (Fintype.card V - 2) ≤ H.edgeSet.ncard := by sorry
