-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_one_step__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
-- name    : WilliamsonShmoys.planar_connected_extension_of_one_step__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:26.0762+00:00
-- url     : https://prove2.me/theorems/1f4c177d-eb20-4750-9a13-0c928226c3d6
-- title:
--   Iterate planar one-edge extensions to connect a finite graph
-- statement:
--   On a finite vertex type, if every planar graph reachable during the construction can be extended by a planar supergraph joining any chosen pair of unreachable vertices, then the original planar graph has a connected planar supergraph on the same vertices that contains all its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_extension_of_one_step__p2m_e072abf9_a18d_4ec4_b40d_84b33bde54a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hstep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ u v : V, ¬ G.Reachable u v →
        ∃ K : SimpleGraph V,
          HasPlanarDrawingOn K ∧ G ≤ K ∧ K.Adj u v) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ H.Connected ∧ M ≤ H := by sorry
