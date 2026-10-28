-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_9f4db670
-- name    : WilliamsonShmoys.maximal_planar_edge_count_9f4db670
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:51:36.249379+00:00
-- url     : https://prove2.me/theorems/a44648d9-0faf-4018-a7f3-53b1a69366ee
-- title:
--   An inclusion-maximal drawable graph has the planar extremal edge count
-- statement:
--   For a drawable simple graph on at least three vertices, having no drawable strict supergraph on the same vertex type forces exactly `3|V|−6` edges. This supplies the edge count used by the parent. A proof route is to show maximality forces connectivity and triangular faces, then apply Euler’s formula and count face-edge incidences. The size hypothesis is necessary: maximal graphs on fewer than three vertices do not generally have this count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_9f4db670
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ K : SimpleGraph V, L.edgeSet ⊂ K.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
