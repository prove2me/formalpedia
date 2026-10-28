-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound_9064c577
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:18:16.143963+00:00
-- url     : https://prove2.me/theorems/7e228393-7108-4591-9f8d-9d9c9dc393b5
-- title:
--   Maximal drawable extension for the planar edge bound
-- statement:
--   Every connected drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that remains connected, is maximal among drawable supergraphs, and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      K.Connected ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
