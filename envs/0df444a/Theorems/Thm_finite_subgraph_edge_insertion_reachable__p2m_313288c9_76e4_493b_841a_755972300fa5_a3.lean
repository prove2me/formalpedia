-- Prove2me | Theorems.Thm_finite_subgraph_edge_insertion_reachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
-- name    : finite_subgraph_edge_insertion_reachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:45:17.289587+00:00
-- url     : https://prove2.me/theorems/829d0f6d-145b-434e-b430-7fcbe8d30408
-- title:
--   Every finite subgraph is reachable by legal edge insertions
-- statement:
--   Every finite subgraph of `G` can be built from the empty graph by finitely many insertions of edges from `G`, each absent from the current graph. The child removes the finite edge construction from the parent; prove it by induction on `H.edgeFinset`, deleting one edge and then reinserting it. With no edges, extensionality identifies `H` with `⊥`. The parent then follows by induction on the insertion sequence. The only remaining core obligation is establishing this finite edge-set induction and the deletion/reinsertion equalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Definitions.Def_EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3

theorem finite_subgraph_edge_insertion_reachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hHG : H ≤ G) :
    EdgeInsertionReachable__p2m_313288c9_76e4_493b_841a_755972300fa5_a3 G H := by sorry
