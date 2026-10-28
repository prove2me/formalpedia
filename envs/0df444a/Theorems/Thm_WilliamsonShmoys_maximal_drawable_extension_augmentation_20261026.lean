-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_augmentation_20261026
-- name    : WilliamsonShmoys.maximal_drawable_extension_augmentation_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:45:21.398755+00:00
-- url     : https://prove2.me/theorems/5e7e0a08-a5de-445b-86ba-39e4ea810e00
-- title:
--   Planar edge augmentation below the bound
-- statement:
--   A finite drawable graph on at least three vertices with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertices. When |V|=3, the hypothesis says it has fewer than three edges, so it can be extended to K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_extension_augmentation_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hE : L.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V, L < M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by
  sorry
