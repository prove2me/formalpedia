-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
-- name    : WilliamsonShmoys.maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:51.891212+00:00
-- url     : https://prove2.me/theorems/b554ef36-a96a-42de-b297-4474260662ac
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices with no strictly larger drawable supergraph on the same vertex set has at least 3|V|−6 edges. Use maximality to establish connectedness and triangular faces, then combine face counting with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by sorry
