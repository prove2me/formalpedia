-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:44.19533+00:00
-- url     : https://prove2.me/theorems/b412dfed-7d75-4614-a7f1-ca8af74bccf6
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex set that is maximal under inclusion among drawable supergraphs. This separates the finite choice of a maximal element from the face-count argument. A proof route is to range over the finite set of simple graphs on V, restrict to drawable extensions of G, and select an inclusion-maximal member. This child removes the maximal-extension choice from the parent; the remaining core obligation is to prove the edge and face equations for such a maximal drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → M = N := by
  sorry
