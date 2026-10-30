-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- name    : WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:34:19.050769+00:00
-- url     : https://prove2.me/theorems/7c886425-c354-41de-891d-80df9a84127f
-- title:
--   Finite hereditary graph properties admit maximal extensions
-- statement:
--   For a finite vertex type, any property of simple graphs preserved under deleting edges has an inclusion-maximal extension of any graph that satisfies it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V → Prop) (hmono : ∀ {G H : SimpleGraph V}, Set.Subset G.edgeSet H.edgeSet → R H → R G) (N : SimpleGraph V) (hN : R N) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ R P ∧ ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → R Q → Set.Subset Q.edgeSet P.edgeSet := by
  sorry
