-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count
-- name    : WilliamsonShmoys.planar_completion_with_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:39:23.224385+00:00
-- url     : https://prove2.me/theorems/d752868c-72d4-41b5-9a5a-f35680a78fe7
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every finite simple planar graph on at least three vertices has a planar supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_with_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
