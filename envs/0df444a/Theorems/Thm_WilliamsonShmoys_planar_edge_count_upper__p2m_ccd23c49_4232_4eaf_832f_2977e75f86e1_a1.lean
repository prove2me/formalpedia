-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:03.146821+00:00
-- url     : https://prove2.me/theorems/9f29656c-dc34-4a7a-a3c2-ff1f2fc6d96d
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every graph with a drawing as defined by `HasPlanarDrawingOn`, on at least three vertices, has at most 3|V|−6 edges. This supplies the upper inequality needed for the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
