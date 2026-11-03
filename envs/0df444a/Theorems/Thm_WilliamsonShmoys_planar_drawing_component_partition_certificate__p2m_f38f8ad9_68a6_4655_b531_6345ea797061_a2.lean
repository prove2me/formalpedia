-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- name    : WilliamsonShmoys.planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:38.871862+00:00
-- url     : https://prove2.me/theorems/8fb060ce-122c-4344-a570-6fdb0412375d
-- title:
--   Partition a planar drawing into connected induced components
-- statement:
--   Decompose the finite graph into nonempty, disjoint connected-component vertex sets covering all vertices. Each induced component of size at least three is connected and inherits the planar drawing; singleton and pair components have zero and at most one edge, respectively. Vertex and edge counts decompose over the blocks. The finite subtype instances are made explicit for induced edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C, 3 ≤ B.card →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected ∧
        HasPlanarDrawingOn (N.induce (↑B : Set V))) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1) ∧
      N.edgeFinset.card =
        ∑ B ∈ C, (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _; (N.induce (↑B : Set V)).edgeFinset.card)) := by sorry
