-- Prove2me | Theorems.Thm_WilliamsonShmoys_extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
-- name    : WilliamsonShmoys.extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:58:58.705996+00:00
-- url     : https://prove2.me/theorems/13580833-cd4c-44e5-a8be-55495eb3e767
-- title:
--   Extract the added edge as an oriented bridge
-- statement:
--   From a drawing of the graph with the added edge, retain the drawing of every original edge and extract the added edge as a simple bridge directed from u to v. Handle either ordering of u and v while preserving the vertex-avoidance and crossing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.extract_added_edge_as_bridge__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (u v : V) (hnot : ¬ H.Reachable u v)
    (hAug : HasPlanarDrawingOn (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)})) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (bridge : ℝ → ℝ × ℝ),
      Function.Injective p ∧
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
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc (0 : ℝ) 1) ∧
      bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
