-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- name    : WilliamsonShmoys.local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:40.1342+00:00
-- url     : https://prove2.me/theorems/62f2497d-bcc3-491f-aebd-6edd152459b6
-- title:
--   An edge across unreachable vertices strictly increases edge count
-- statement:
--   If H extends G by exactly the edge between u and v, and u and v were unreachable in G, then H has strictly more edges than G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : ¬ G.Reachable u v)
    (H : SimpleGraph V) (hGH : G ≤ H)
    (hadj : ∀ x y : V,
      H.Adj x y ↔
        G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
