-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:18.542086+00:00
-- url     : https://prove2.me/theorems/c3c9ffa7-0ab4-4781-8a7b-d6d91ceb974a
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal finite planar simple graph on at least three vertices has at least 3|V|−6 edges. The source argument is that if a face is not triangular, a missing edge can be drawn inside it, contradicting maximality; hence all faces are triangular, and Euler’s formula gives the count. This child isolates the maximality-driven lower bound and removes the augmentation/face-triangulation work from the parent. Its remaining core is to establish that the supplied arc drawing admits the relevant face argument and that maximality rules out every nontriangular face, including boundary and connectivity cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset → K.edgeFinset = L.edgeFinset) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  sorry
