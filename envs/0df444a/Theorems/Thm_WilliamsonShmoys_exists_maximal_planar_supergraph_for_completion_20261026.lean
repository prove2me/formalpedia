-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_completion_20261026
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_completion_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:08:58.434321+00:00
-- url     : https://prove2.me/theorems/ef69c269-0993-4e7a-b0bd-d6178914af6f
-- title:
--   Existence of a maximal drawable supergraph on the same vertices
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable supergraphs. The family is finite and nonempty, so a member with the greatest edge count has the required maximality: any proper drawable extension would have strictly more edges. This child removes the maximal-extension existence step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_completion_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V, M ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M := by sorry
