-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:54.571804+00:00
-- url     : https://prove2.me/theorems/558e4c7b-93a1-4c08-9af2-8975677e8b56
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
