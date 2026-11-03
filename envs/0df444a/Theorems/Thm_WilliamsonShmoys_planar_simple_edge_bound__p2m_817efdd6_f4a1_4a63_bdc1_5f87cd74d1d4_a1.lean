-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
-- name    : WilliamsonShmoys.planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:52.555837+00:00
-- url     : https://prove2.me/theorems/e743f516-2fe6-4f90-ae81-e51127ac517d
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple graph on at least three vertices with the supplied planar drawing has at most 3V − 6 edges. This supplies the standard planar extremal estimate needed alongside Euler's formula; a proof can count edge sides around faces and use simplicity to bound face boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound__p2m_817efdd6_f4a1_4a63_bdc1_5f87cd74d1d4_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
