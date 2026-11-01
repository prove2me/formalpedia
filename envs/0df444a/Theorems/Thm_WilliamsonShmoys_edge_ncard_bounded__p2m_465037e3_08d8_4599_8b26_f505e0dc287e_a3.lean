-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- name    : WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:12.751324+00:00
-- url     : https://prove2.me/theorems/378afc0d-9fde-4afd-b748-1fd74abdceed
-- title:
--   Graph edge count is bounded by unordered vertex pairs
-- statement:
--   Every graph edge is an unordered pair of vertices, so its edge set is contained in the finite type Sym2 V. This supplies the measure bound required by the maximal-witness child and removes that bound proof from the parent. Prove it by viewing edgeSet as a subset of Set.univ and applying the finite-set cardinality bound. When V is empty, both the edge count and the bound are zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by sorry
