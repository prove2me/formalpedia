-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_local_edge_bounds__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
-- name    : WilliamsonShmoys.planar_drawing_component_local_edge_bounds__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:02.29645+00:00
-- url     : https://prove2.me/theorems/6bc429f4-cd56-45b3-a75d-d680b9b59131
-- title:
--   Local induced-edge bounds for each component block
-- statement:
--   For each block, the induced edge count is at most three times the block size; blocks of size at least three satisfy the stronger estimate with additive slack six. Large blocks use the connected planar bound and transfer the subtype cardinality to the block cardinality; singleton and pair blocks use their supplied edge estimates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_component_local_edge_bounds__p2m_a70877ba_ee67_4eb5_a950_6d5f423393ca_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (C : Finset (Finset V))
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hW : 3 ≤ Fintype.card W)
      (hconn : G.Connected) (hG : HasPlanarDrawingOn G),
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset.card + 6 ≤ 3 * Fintype.card W))
    (hbig : ∀ B ∈ C, 3 ≤ B.card →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).Connected ∧
      HasPlanarDrawingOn (N.induce (↑B : Set V)))
    (hsingle : ∀ B ∈ C, B.card = 1 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card = 0)
    (hpair : ∀ B ∈ C, B.card = 2 →
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card ≤ 1) :
    ∀ B ∈ C,
      letI : DecidableRel N.Adj := Classical.decRel N.Adj
      letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
      (N.induce (↑B : Set V)).edgeFinset.card ≤ 3 * B.card ∧
      (3 ≤ B.card →
        (N.induce (↑B : Set V)).edgeFinset.card + 6 ≤ 3 * B.card) := by sorry
