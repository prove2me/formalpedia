-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_bridge_extensions
-- name    : WilliamsonShmoys.iterate_bridge_extensions
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:24:57.326314+00:00
-- url     : https://prove2.me/theorems/86f599f4-bd8e-4c40-aa6d-2c1496ff28ba
-- title:
--   Finite iteration of planar bridge extensions
-- statement:
--   Repeatedly apply the assumed bridge extension to a disconnected planar graph. Since every step adds a new edge and the vertex type is finite, the process yields a connected planar supergraph containing the initial graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.iterate_bridge_extensions
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (bridge_extension : ∀ (J : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn J →
      ¬ (∀ u v : V, Nonempty (J.Walk u v)) →
      ∃ L : SimpleGraph V,
        J ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (J.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
