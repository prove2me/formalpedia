-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_large_e9dfd49a
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_large_e9dfd49a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:07:43.224168+00:00
-- url     : https://prove2.me/theorems/9dbc1b44-5e81-4cbc-9338-84418c6013a1
-- title:
--   Connect a sufficiently large planar drawing by adding edges
-- statement:
--   For a finite drawn graph with at least three vertices, there is a connected planar supergraph on the same vertex set that retains every original edge, so its edge count is no smaller.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_extension_large_e9dfd49a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by sorry
