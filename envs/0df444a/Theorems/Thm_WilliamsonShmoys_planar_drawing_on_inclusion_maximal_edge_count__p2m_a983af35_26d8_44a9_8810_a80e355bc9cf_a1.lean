-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- name    : WilliamsonShmoys.planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:57.320313+00:00
-- url     : https://prove2.me/theorems/4dcc8868-a279-4e00-9c27-a17d1a75556d
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges. This isolates the planar topology and Euler-counting work; a proof route is to show maximality forces connectedness and triangular faces, then count incidences using Euler’s formula. The strict size hypothesis is retained for the small-vertex boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_inclusion_maximal_edge_count__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U) (hmax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W ≤ U) : 3 * Fintype.card V - 6 = U.edgeSet.ncard := by
  sorry
