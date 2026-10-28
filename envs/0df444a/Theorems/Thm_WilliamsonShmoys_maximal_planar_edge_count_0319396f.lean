-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_0319396f
-- name    : WilliamsonShmoys.maximal_planar_edge_count_0319396f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:32:58.918482+00:00
-- url     : https://prove2.me/theorems/ce473880-b212-439c-9a31-ff5d9cae8ffe
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges. The size hypothesis includes the three-vertex complete-graph boundary case. This child isolates the topological core: show maximality forces a triangulation and use Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_0319396f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
