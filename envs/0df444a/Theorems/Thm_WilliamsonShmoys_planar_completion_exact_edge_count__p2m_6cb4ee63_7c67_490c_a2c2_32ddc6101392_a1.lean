-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1
-- name    : WilliamsonShmoys.planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:43.093959+00:00
-- url     : https://prove2.me/theorems/bbef08b9-09b8-4a50-88ab-5b845e32b992
-- title:
--   Completion of a drawable graph to the maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
