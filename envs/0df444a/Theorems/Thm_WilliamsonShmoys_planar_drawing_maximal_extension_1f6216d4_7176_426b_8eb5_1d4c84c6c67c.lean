-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:19:48.109946+00:00
-- url     : https://prove2.me/theorems/97bdc2f3-bd08-4552-a397-56b8a3780a24
-- title:
--   Finite maximality yields a connected drawn extension
-- statement:
--   If every disconnected drawn supergraph of `H` admits a drawn supergraph with strictly more edges, then `H` has a connected drawn supergraph. Choose a maximum-edge member from the finite collection of drawn supergraphs containing `H`; `hstep` rules out its being disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hstep : ∀ G : SimpleGraph V, H ≤ G →
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          G.edgeSet.ncard < K.edgeSet.ncard) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
