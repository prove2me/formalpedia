-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- name    : WilliamsonShmoys.planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:14.480624+00:00
-- url     : https://prove2.me/theorems/468912c8-f62d-4992-8d85-065aef654ab4
-- title:
--   Insert an edge along a disjoint curve
-- statement:
--   Given a planar drawing and a continuous injective curve between two distinct nonadjacent vertices whose interior avoids all drawn vertices and existing edge arcs, construct a planar supergraph on the same vertices with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_extend_from_curve__p2m_30cabda6_8091_40b2_a533_c24aec10a077_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p) (hEdge : ∀ a b, a < b → G.Adj a b → ContinuousOn (arc a b) (Set.Icc 0 1) ∧ Set.InjOn (arc a b) (Set.Icc 0 1) ∧ arc a b 0 = p a ∧ arc a b 1 = p b ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) (hCross : ∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y → (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) (u v : V) (huv : u < v) (hnot : ¬ G.Adj u v) (γ : ℝ → ℝ × ℝ) (hγ_cont : ContinuousOn γ (Set.Icc 0 1)) (hγ_inj : Set.InjOn γ (Set.Icc 0 1)) (hγ_start : γ 0 = p u) (hγ_end : γ 1 = p v) (hγ_vertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w) (hγ_edges : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y → ∀ s ∈ Set.Icc (0 : ℝ) 1, γ t ≠ arc x y s) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ G.edgeSet.ncard < K.edgeSet.ncard := by sorry
