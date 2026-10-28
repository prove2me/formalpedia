-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_8a86a385
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension_8a86a385
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:15:43.203978+00:00
-- url     : https://prove2.me/theorems/047b886c-57fd-4d60-8296-d1283c51605e
-- title:
--   Finite maximal planar extension
-- statement:
--   Every connected finite graph with a drawing satisfying HasPlanarDrawingOn has a connected planar supergraph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension_8a86a385
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
