-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49
-- name    : WilliamsonShmoys.maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:08:25.049053+00:00
-- url     : https://prove2.me/theorems/3fe6515b-8335-4a72-a208-f1a2ec6f6eaf
-- title:
--   The edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has exactly `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_count_43124a08_e00c_4a1a_ad63_e868e93f9e49 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hmax : WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
