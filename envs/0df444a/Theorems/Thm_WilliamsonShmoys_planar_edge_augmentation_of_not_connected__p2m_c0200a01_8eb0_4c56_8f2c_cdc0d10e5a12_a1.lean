-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:02.186999+00:00
-- url     : https://prove2.me/theorems/14681c25-312c-4d7a-aa72-c2f717bd3325
-- title:
--   A disconnected planar drawing admits a strict drawable edge extension
-- statement:
--   For a finite ordered vertex type with at least three vertices, if a graph has a crossing-free drawing and is disconnected, there are distinct nonadjacent vertices that can be joined in a strict supergraph which still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U) (hdisc : ¬ U.Connected) : ∃ (a b : V) (W : SimpleGraph V), a ≠ b ∧ ¬ U.Adj a b ∧ U ≤ W ∧ W ≠ U ∧ W.Adj a b ∧ HasPlanarDrawingOn W := by sorry
