-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_7f31c9a2
-- name    : WilliamsonShmoys.planar_edge_count_completion_7f31c9a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:10:50.670596+00:00
-- url     : https://prove2.me/theorems/c3d7847a-cbe5-4eb5-8f30-87b0749479c4
-- title:
--   Drawable extension with the maximal planar edge count
-- statement:
--   Every drawable simple graph on at least three finite linearly ordered vertices extends, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges. The child packages planar completion and the Euler edge count; the parent uses the supplied maximality hypothesis to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_completion_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
