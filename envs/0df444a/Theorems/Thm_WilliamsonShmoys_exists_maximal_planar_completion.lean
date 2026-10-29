-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion
-- name    : WilliamsonShmoys.exists_maximal_planar_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:54:16.230144+00:00
-- url     : https://prove2.me/theorems/d95dba66-5420-4b02-a872-5317ddf9e659
-- title:
--   Maximal drawable completion reaches the planar bound
-- statement:
--   A drawable finite simple graph on at least three vertices has a drawable supergraph maximal among drawable supergraphs on the same vertex type, with exactly `3 * |V| - 6` edges. The size hypothesis is needed for the planar edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
