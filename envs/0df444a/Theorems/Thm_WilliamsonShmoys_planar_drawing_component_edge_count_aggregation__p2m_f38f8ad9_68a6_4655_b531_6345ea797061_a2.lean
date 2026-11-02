-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- name    : WilliamsonShmoys.planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:43.758369+00:00
-- url     : https://prove2.me/theorems/a70877ba-ee67-4eb5-a950-6d5f423393ca
-- title:
--   Aggregate edge bounds over planar components
-- statement:
--   Given a partition with the stated block properties and edge-count decomposition, the connected planar bound on blocks of size at least three implies the bound for the whole graph. Small blocks contribute their direct simple-graph bounds; the case with no large block follows from the total vertex lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj] (hV : 3 ≤ Fintype.card V)
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hW : 3 ≤ Fintype.card W)
      (hconn : G.Connected) (hG : HasPlanarDrawingOn G),
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset.card + 6 ≤ 3 * Fintype.card W))
    (C : Finset (Finset V))
    (hpos : ∀ B ∈ C, 0 < B.card)
    (hdisj : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
      Disjoint (↑B₁ : Set V) (↑B₂ : Set V))
    (hcover : ∀ v : V, ∃ B ∈ C, v ∈ B)
    (hcard : Fintype.card V = ∑ B ∈ C, B.card)
    (hbig : ∀ B ∈ C, 3 ≤ B.card →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj; letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).Connected ∧
      HasPlanarDrawingOn (N.induce (↑B : Set V)))
    (hsingle : ∀ B ∈ C, B.card = 1 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj; letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card = 0)
    (hpair : ∀ B ∈ C, B.card = 2 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj; letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card ≤ 1)
    (hedge : N.edgeFinset.card =
      ∑ B ∈ C, (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _; (N.induce (↑B : Set V)).edgeFinset.card)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
