-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- name    : WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:14.416192+00:00
-- url     : https://prove2.me/theorems/a47d675c-d853-4366-9b4e-a6f16812a71d
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Any graph with a crossing-free drawing can be extended, without adding vertices, to a connected graph that still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : ∃ U : SimpleGraph V, T ≤ U ∧ U.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn U := by sorry
