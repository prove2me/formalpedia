-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- name    : WilliamsonShmoys.planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:36.857803+00:00
-- url     : https://prove2.me/theorems/e59f08ac-c69e-4607-8c7d-4507b335dcb0
-- title:
--   Finite iteration of strict planar extensions
-- statement:
--   If every disconnected planar graph on this finite vertex type admits a strict planar supergraph, then repeated extensions yield a connected planar supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (extend : forall (G : SimpleGraph V), HasPlanarDrawingOn G -> Not G.Connected ->
      Exists fun K : SimpleGraph V => And (LE.le G K) (And (Not (G = K)) (HasPlanarDrawingOn K))) :
    Exists fun K : SimpleGraph V => And (LE.le H K) (And K.Connected (HasPlanarDrawingOn K)) := by sorry
