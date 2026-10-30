-- Prove2me | Theorems.Thm_WilliamsonShmoys_graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- name    : WilliamsonShmoys.graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:51.150377+00:00
-- url     : https://prove2.me/theorems/d35fda82-8541-4dc1-89a0-c862b4fc5d32
-- title:
--   Finite graph inclusion from edge-count comparison
-- statement:
--   For finite graphs on the same vertex type, edge-set inclusion together with the reverse inequality of edge counts implies reverse edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    H.edgeSet ⊆ G.edgeSet := by
  sorry
