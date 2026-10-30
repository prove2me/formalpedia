-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:39.002619+00:00
-- url     : https://prove2.me/theorems/6cb4ee63-7c67-490c-a2c2-32ddc6101392
-- title:
--   Edge count of a drawable maximal planar graph
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices that has no drawable proper supergraph on those vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hmaximal : ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
