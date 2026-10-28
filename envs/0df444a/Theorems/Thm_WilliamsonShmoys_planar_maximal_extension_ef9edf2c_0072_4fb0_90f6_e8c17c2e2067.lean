-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- name    : WilliamsonShmoys.planar_maximal_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:08:58.631099+00:00
-- url     : https://prove2.me/theorems/759bb822-5363-49a9-a009-8ba97a974de2
-- title:
--   Extend a drawable graph to an edge-maximal drawable graph
-- statement:
--   Starting from any drawable graph on a finite ordered vertex type, produce a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. This removes the finite augmentation and witness-selection step from the parent. No existing formal proof was available to inspect; the new argument is to consider all drawable edge-set extensions of G, a nonempty finite collection, and choose an inclusion-maximal member. The base graph G witnesses nonemptiness, and finiteness of the possible edges gives maximality. Drawing heredity ensures the chosen graph belongs to the collection. There is no lower bound on the vertex count in this lemma, so it also covers empty vertex types and the empty graph. The proof must formalize heredity and the finite maximal-choice argument for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
