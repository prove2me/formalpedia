-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
-- name    : WilliamsonShmoys.strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:47.475204+00:00
-- url     : https://prove2.me/theorems/c631ba2b-35bf-4e56-b4a3-6b95fe41ac1e
-- title:
--   Strict subgraph inclusion increases finite edge count
-- statement:
--   If one finite-edge-set simple graph is a proper subgraph of another, its edge finset has strictly smaller cardinality. This supplies the measure-growth hypothesis required by the generic maximal-extension child. The proof route is to derive `G < H` from inclusion and inequality, use Mathlib’s characterization of strict inclusion by `edgeFinset` strict subset, and apply strict cardinal growth for finite sets. The explicit edge-set finiteness instances address the latest compiler diagnostic; the parent can infer them under classical decidability on a finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.strict_edge_card_of_strict_subgraph__p2m_6dfd0e85_ae5a_4e02_9c9b_5863f1785ef0_a2
    {V : Type} [Fintype V]
    {G H : SimpleGraph V} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hGH : G ≤ H) (hne : G ≠ H) :
    G.edgeFinset.card < H.edgeFinset.card := by sorry
