-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_not_connected
-- name    : WilliamsonShmoys.exists_drawable_strict_supergraph_of_not_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:04:07.824571+00:00
-- url     : https://prove2.me/theorems/15f889c3-2e0e-4106-aa2c-3a5f9bf4a647
-- title:
--   A disconnected drawable graph has a drawable strict supergraph
-- statement:
--   Every disconnected graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has a drawable strict supergraph on that same vertex type. This isolates the geometric augmentation step needed by maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_strict_supergraph_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ G := by
  sorry
