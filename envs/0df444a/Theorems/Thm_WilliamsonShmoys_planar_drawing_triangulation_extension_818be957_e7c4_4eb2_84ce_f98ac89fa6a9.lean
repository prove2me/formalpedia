-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:01:40.188679+00:00
-- url     : https://prove2.me/theorems/e83443cd-7838-4846-ac2b-89eeadfab59c
-- title:
--   Triangulate a planar drawing on the same vertices
-- statement:
--   Every crossing-free drawing on at least three vertices extends to a crossing-free drawing of a supergraph on the same vertices with exactly `3|V| - 6` edges. The parent uses the target’s strict edge-count bound to show this extension differs from the original graph. Proving the child requires formalizing edge insertion within faces, handling disconnected drawings, and deriving the edge count from Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_818be957_e7c4_4eb2_84ce_f98ac89fa6a9
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V,
      G ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
