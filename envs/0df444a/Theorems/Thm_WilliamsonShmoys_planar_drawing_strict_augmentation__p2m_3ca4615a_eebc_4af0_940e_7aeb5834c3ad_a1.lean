-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- name    : WilliamsonShmoys.planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:37.28019+00:00
-- url     : https://prove2.me/theorems/62655122-fd0a-4865-bebb-51bfbf1c6569
-- title:
--   Strict planar augmentation below the triangulation bound
-- statement:
--   If a finite simple graph on at least three vertices has a drawing satisfying HasPlanarDrawingOn and fewer than 3|V|−6 edges, it has a strictly larger planar simple supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_strict_augmentation__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hE : (letI : DecidableRel M.Adj := Classical.decRel M.Adj
           M.edgeFinset.card) < 3 * Fintype.card V - 6) :
    ∃ M' : SimpleGraph V, HasPlanarDrawingOn M' ∧ M ≤ M' ∧ M' ≠ M := by sorry
