-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_e9dfd49a
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_e9dfd49a
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T22:13:48.984928+00:00
-- url     : https://prove2.me/theorems/bf80fae6-7e8c-467f-a9f1-c1875eb4998a
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   Any finite graph with the given crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing, retaining every original edge. Therefore its edge count does not decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_e9dfd49a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by sorry
