-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- name    : WilliamsonShmoys.maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:39:12.363781+00:00
-- url     : https://prove2.me/theorems/1927a2f2-efe0-4e83-ba03-5beb334dbd6d
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An edge-maximal graph under the given finite drawing predicate, with at least three vertices, has at least 3|V|−6 edges. Prove by showing maximality forces a triangulated planar embedding, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edgeSet_ncard_ge_three_mul_card_sub_six__p2m_b8afd70d_5e18_4708_a739_37d2bdc4e576_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
