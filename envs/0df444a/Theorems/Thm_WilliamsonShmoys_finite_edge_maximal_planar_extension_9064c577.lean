-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edge_maximal_planar_extension_9064c577
-- name    : WilliamsonShmoys.finite_edge_maximal_planar_extension_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:45:57.624784+00:00
-- url     : https://prove2.me/theorems/704124e6-dd14-4fd4-a7de-4dc973009b44
-- title:
--   Finite edge-maximal planar extension
-- statement:
--   On a finite linearly ordered vertex type, every drawable graph has a drawable supergraph maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_edge_maximal_planar_extension_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) := by sorry
