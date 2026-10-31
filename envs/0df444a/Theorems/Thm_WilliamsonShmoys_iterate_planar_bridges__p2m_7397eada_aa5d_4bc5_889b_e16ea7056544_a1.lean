-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
-- name    : WilliamsonShmoys.iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:16.027764+00:00
-- url     : https://prove2.me/theorems/a6c61c44-359d-4d57-8094-2c2773f7c78b
-- title:
--   Iterate finite planar edge extensions to connect
-- statement:
--   If every planar supergraph of the initial finite graph that is disconnected has a planar supergraph with strictly more edges, then a connected planar supergraph exists. Prove this by finite induction on the number of possible edges (bounded by the finite vertex type); each extension strictly increases the edge count, so iteration cannot continue indefinitely. This separates the finite termination and graph-order argument from the geometric bridge construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.iterate_planar_bridges__p2m_7397eada_aa5d_4bc5_889b_e16ea7056544_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hstep : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → ¬ K.Connected → ∃ L : SimpleGraph V, K ≤ L ∧ K.edgeSet.ncard < L.edgeSet.ncard ∧ HasPlanarDrawingOn L) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G := by sorry
