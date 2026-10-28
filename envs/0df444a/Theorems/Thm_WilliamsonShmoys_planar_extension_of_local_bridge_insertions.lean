-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_of_local_bridge_insertions
-- name    : WilliamsonShmoys.planar_extension_of_local_bridge_insertions
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:24:51.004991+00:00
-- url     : https://prove2.me/theorems/54627add-0887-465a-9dc2-112defe1c0ac
-- title:
--   Iterate planar bridge insertions to connect a finite graph
-- statement:
--   If every disconnected drawable graph admits a drawable single-edge insertion joining distinct components and retaining all existing edges, repeatedly insert such edges until the graph is connected. Finite edge capacity guarantees termination and edge count never decreases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_of_local_bridge_insertions
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ u v : V, ∃ L : SimpleGraph V,
        ¬ K.Reachable u v ∧
        ¬ K.Adj u v ∧
        L.Adj u v ∧
        (∀ x y, K.Adj x y → L.Adj x y) ∧
        (∀ x y, L.Adj x y →
          K.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
        WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
