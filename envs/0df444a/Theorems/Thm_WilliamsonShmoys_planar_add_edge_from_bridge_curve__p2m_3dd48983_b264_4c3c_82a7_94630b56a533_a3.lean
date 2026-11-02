-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- name    : WilliamsonShmoys.planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:42:05.556216+00:00
-- url     : https://prove2.me/theorems/87e40efa-8693-4cd1-a831-8cf8bfa1bc8f
-- title:
--   Add an edge along a bridge curve
-- statement:
--   Given a planar drawing and a simple curve from u to v whose interior avoids vertices and whose intersections with existing edges occur only at endpoints, extend the graph with edge uv while preserving planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V}
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (gamma : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hedge : ∀ a b, a < b → G.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hdisjoint : ∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
      (a, b) ≠ (c, d) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc c d s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hstart : gamma 0 = p u) (hend : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hedge_intersections : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
