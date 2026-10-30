-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_strict_extension_of_unreachable__p2m_8c53f87a_b244_43b9_9258_2c83805c4d13_a2
-- name    : WilliamsonShmoys.planar_drawingOn_strict_extension_of_unreachable__p2m_8c53f87a_b244_43b9_9258_2c83805c4d13_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:48.773951+00:00
-- url     : https://prove2.me/theorems/a2150ff6-574b-4cf9-a3b6-63742a3d1c33
-- title:
--   A drawable graph with unreachable distinct vertices has a drawable strict extension
-- statement:
--   If a finite drawable graph has two distinct unreachable vertices, it has a drawable strict supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_strict_extension_of_unreachable__p2m_8c53f87a_b244_43b9_9258_2c83805c4d13_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    {u v : V} (huv : u ≠ v) (hUnreach : ¬ L.Reachable u v) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧ ¬ M ≤ L := by sorry
