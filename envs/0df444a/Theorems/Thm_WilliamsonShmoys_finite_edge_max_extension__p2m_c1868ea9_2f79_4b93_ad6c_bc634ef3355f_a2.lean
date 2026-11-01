-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- name    : WilliamsonShmoys.finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:37.46434+00:00
-- url     : https://prove2.me/theorems/083ca99e-2b17-4168-b930-bae4acf23658
-- title:
--   Finite maximal edge-count extension
-- statement:
--   Among the property-preserving supergraphs of K, there is one whose edge count is maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V,
      P H ∧ K ≤ H ∧
        ∀ G : SimpleGraph V, P G → K ≤ G →
          G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
