-- Prove2me | Theorems.Thm_WilliamsonShmoys_extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2
-- name    : WilliamsonShmoys.extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:44:44.014764+00:00
-- url     : https://prove2.me/theorems/b73d0dc0-bd45-4d41-a154-c497fe2a40b3
-- title:
--   Extract an oriented bridge from an augmented drawing witness
-- statement:
--   Given a fixed augmented drawing witness for the graph formed by adding the edge `{u,v}`, retain its original-edge drawing data and extract a simple bridge from `u` to `v` that avoids all vertices in its interior and meets original edge arcs only at endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.extract_added_edge_as_bridge_geometric_core__p2m_13580833_cd4c_44e5_a8be_55495eb3e767_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hAugEdge : ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hAugCross : ∀ a b x y, a < b → x < y →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj a b →
      (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hnot : ¬ H.Reachable u v) :
    (∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
    (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
    ∃ bridge : ℝ → ℝ × ℝ,
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
