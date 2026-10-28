-- Prove2me | Theorems.Thm_simpleGraph_eq_of_edge_ncard_le
-- name    : simpleGraph_eq_of_edge_ncard_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:55:01.168749+00:00
-- url     : https://prove2.me/theorems/6b7d614d-4bd6-4221-9f2f-be08782aca52
-- title:
--   Graph equality from inclusion and edge cardinality
-- statement:
--   For finite simple graphs, inclusion together with the reverse edge-count inequality forces equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_eq_of_edge_ncard_le
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (hGH : ∀ u v, G.Adj u v → H.Adj u v)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    G = H := by sorry
