-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
-- name    : WilliamsonShmoys.planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:31.540015+00:00
-- url     : https://prove2.me/theorems/a8601a7b-3dd5-4a47-bc32-8f856380985e
-- title:
--   Saturate a finite planar drawing without adding vertices
-- statement:
--   Every finite simple graph with at least three vertices that has the specified crossing-free drawing can be extended, without changing its vertex set, to a drawn simple planar supergraph with exactly 3|V|−6 edges; the original graph’s edge count is at most that of the extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_saturated_supergraph__p2m_0cbdf370_052c_4f7e_80db_29586f4df68b_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
