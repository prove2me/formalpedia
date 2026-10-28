-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:47:52.802523+00:00
-- url     : https://prove2.me/theorems/039d0646-cb25-42f8-8fce-e602db1c661b
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   A finite graph with a planar drawing and at least three vertices has a connected planar supergraph on the same vertex set that retains every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected := by sorry
