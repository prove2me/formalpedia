-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- name    : WilliamsonShmoys.simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:50.284255+00:00
-- url     : https://prove2.me/theorems/c92ac6a0-7247-4790-a784-667c7517ebb5
-- title:
--   Inclusion and edge-count bound force simple graph equality
-- statement:
--   If one finite simple graph contains another and has no more edges, the graphs are equal. This removes the parent’s maximality step: apply it to K and any drawable supergraph L, using the maximizer child for the edge-count bound. Prove by viewing edge sets as finite sets, using inclusion and cardinality, then extensionality. No positivity or nonempty-vertex hypothesis is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
    {V : Type} [Fintype V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L)
    (hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    L = K := by sorry
