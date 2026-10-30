-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_77f664a0
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_77f664a0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:51:23.42988+00:00
-- url     : https://prove2.me/theorems/e11d7253-3796-4093-8ab6-39cc42890bbd
-- title:
--   Edge count of a maximal finite planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly `3|V| − 6` edges. This isolates the topological core. An independent proof route is to derive connectedness and triangular faces from maximality, then count edge-face incidences and apply Euler’s formula; the three-vertex boundary is retained explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_77f664a0
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
