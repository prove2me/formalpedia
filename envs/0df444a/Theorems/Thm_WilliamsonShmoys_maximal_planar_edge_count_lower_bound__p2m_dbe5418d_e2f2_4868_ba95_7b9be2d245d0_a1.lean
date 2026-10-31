-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- name    : WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:04.131335+00:00
-- url     : https://prove2.me/theorems/00590216-3bdf-4c63-b52e-9e355ea90f1e
-- title:
--   Lower bound forced by maximal planarity
-- statement:
--   A maximal finite simple planar graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) (hKmax : ∀ L : SimpleGraph V, LE.le K L → WilliamsonShmoys.HasPlanarDrawingOn L → LE.le L K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
