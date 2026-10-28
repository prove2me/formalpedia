-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cc20b238_bb42_45fd_bcfd_09a78f307735
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_cc20b238_bb42_45fd_bcfd_09a78f307735
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:00:25.712917+00:00
-- url     : https://prove2.me/theorems/74f17545-4700-4b4e-bbb8-1272e6b92c84
-- title:
--   Choose a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_cc20b238_bb42_45fd_bcfd_09a78f307735
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L → L = K) := by sorry
