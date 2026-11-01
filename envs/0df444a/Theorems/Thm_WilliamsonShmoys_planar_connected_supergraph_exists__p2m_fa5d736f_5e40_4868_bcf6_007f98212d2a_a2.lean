-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
-- name    : WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:37.597007+00:00
-- url     : https://prove2.me/theorems/5d1dfa1d-991a-49fd-b455-4945d33b9ed1
-- title:
--   Connect a nontrivial planar graph without adding vertices
-- statement:
--   This corrects the prior child by preserving the parent’s vertex-count hypothesis, which rules out the empty-vertex counterexample to connectedness. It removes disconnected-component handling from the parent. A proof route is to use the common unbounded face of the finitely many drawn components and add noncrossing arcs between components until connected, extending the arc assignment while retaining the drawing conditions. The lower bound also handles the singleton and two-vertex boundary cases by excluding them; already-connected graphs need no added edges. The remaining core work is to formalize the topological arc construction from the given drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_exists__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
