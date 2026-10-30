-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- name    : WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:02.211839+00:00
-- url     : https://prove2.me/theorems/dbe5418d-e2f2-4868-ba95-7b9be2d245d0
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite maximal planar graph on at least three vertices has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) (hKmax : ∀ L : SimpleGraph V, LE.le K L → WilliamsonShmoys.HasPlanarDrawingOn L → LE.le L K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
