-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_b74a49f4
-- name    : WilliamsonShmoys.planar_connected_supergraph_b74a49f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:48:52.17889+00:00
-- url     : https://prove2.me/theorems/d8347adf-b8e6-4fde-a5c0-1fc7cf33f799
-- title:
--   Connect a planar drawing without losing edges
-- statement:
--   A drawable finite graph on at least three vertices has a connected drawable supergraph on the same vertex set containing all its edges. Prove this by repeatedly joining distinct embedded components with arcs in the complement; because the components are finite and disjoint, each new arc can be chosen to avoid existing vertices and edges except at its endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
