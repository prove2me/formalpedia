-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:12.608202+00:00
-- url     : https://prove2.me/theorems/bca86cba-41f0-4055-99a7-a4513f99a433
-- title:
--   Connecting the components of a crossing-free drawing
-- statement:
--   A graph on at least three finite ordered vertices with a `HasPlanarDrawingOn` drawing is a subgraph of a connected graph on the same vertices that also has a `HasPlanarDrawingOn` drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
