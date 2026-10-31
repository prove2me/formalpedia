-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:34.377175+00:00
-- url     : https://prove2.me/theorems/06ff79b1-005f-4343-ad7e-d750b7a6fe7f
-- title:
--   Maximal drawable extension on a finite vertex set
-- statement:
--   Any drawable graph on a finite vertex set has a drawable supergraph on that same vertex set that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
