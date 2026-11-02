-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_data__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:39.724501+00:00
-- url     : https://prove2.me/theorems/6360b5b8-545a-4187-945d-5d0aa3896a85
-- title:
--   Euler face data for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, establish Euler's vertex-edge-face relation and the total directed edge-incidence count. This removes the topological face-counting and double-incidence work from the parent. A concrete proof route is to extract the cyclic order of incident edges at each vertex, define faces as cycles of the induced dart permutation, and prove Euler's formula for the resulting connected rotation system; each undirected edge contributes two darts. This route must account for trees and bridges, whose face boundary walks may traverse an edge twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_data__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ f l : Nat, Fintype.card V + f = K.edgeFinset.card + 2 ∧ l = 2 * K.edgeFinset.card := by sorry
