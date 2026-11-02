-- Prove2me | Theorems.Thm_edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2
-- name    : edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:37.401296+00:00
-- url     : https://prove2.me/theorems/903bafc1-6bb8-4baa-899c-884ea3fe2615
-- title:
--   Adding a missing adjacency strictly increases the finite edge count
-- statement:
--   If two finite graphs have explicit finite instances for their edge-set subtypes, H contains every edge of G, and H adds an adjacency whose endpoints have no walk in G, then H has strictly more edges than G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open SimpleGraph

theorem edgeFinset_card_strict_of_extension__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a2
    {V : Type} [Fintype V] (G H : SimpleGraph V)
    [Fintype {e // e ∈ G.edgeSet}] [Fintype {e // e ∈ H.edgeSet}]
    (u v : V) (hsub : G.edgeFinset ⊆ H.edgeFinset)
    (hAdj : H.Adj u v) (hwalk : ¬ Nonempty (G.Walk u v)) :
    G.edgeFinset.card < H.edgeFinset.card := by sorry
