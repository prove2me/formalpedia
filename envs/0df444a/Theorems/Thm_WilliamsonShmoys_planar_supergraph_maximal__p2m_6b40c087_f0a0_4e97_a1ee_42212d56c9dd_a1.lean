-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:41.622015+00:00
-- url     : https://prove2.me/theorems/ce3aa1c9-ccc6-4e9e-a3c5-6ecee73dbfd3
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite planar graph on the same ordered vertex type has a planar supergraph that is inclusion-maximal among planar supergraphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_6b40c087_f0a0_4e97_a1ee_42212d56c9dd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) := by sorry
