-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_has_edge_bound
-- name    : WilliamsonShmoys.maximal_drawable_extension_has_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:36:32.369982+00:00
-- url     : https://prove2.me/theorems/424eee2f-0242-4626-9478-f3399c7c1057
-- title:
--   A maximal drawable graph attains the planar edge bound
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_extension_has_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
