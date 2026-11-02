-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
-- name    : WilliamsonShmoys.planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:14.555964+00:00
-- url     : https://prove2.me/theorems/a6ee2644-08f0-4c4d-a139-48d0925fab45
-- title:
--   Iterate planar bridges to obtain a connected supergraph
-- statement:
--   Assume every disconnected drawn graph on the fixed finite ordered vertex type can be extended by one edge between unreachable vertices while preserving a drawing. Then any drawn graph on that type has a connected planar supergraph. The proof iterates the bridge operation, using finiteness to ensure the component count decreases at each step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_bridge_iteration__p2m_711af4b4_5214_45eb_bc71_e82c24cc238b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (bridge : ∀ (G : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
        ∃ u v : V, ¬ G.Reachable u v ∧
          ∃ P : SimpleGraph V,
            (∀ x y : V, P.Adj x y ↔
              G.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
            WilliamsonShmoys.HasPlanarDrawingOn P)
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ P.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
