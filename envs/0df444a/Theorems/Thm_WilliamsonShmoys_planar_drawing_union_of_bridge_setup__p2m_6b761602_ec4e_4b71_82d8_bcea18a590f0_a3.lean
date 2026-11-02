-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
-- name    : WilliamsonShmoys.planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:43:24.711839+00:00
-- url     : https://prove2.me/theorems/ca2a92bc-8b5e-4bfc-b135-48ef776a9947
-- title:
--   Extend a planar drawing using explicit bridge data
-- statement:
--   Explicit crossing-free drawing data for the old graph and an admissible bridge yield a planar drawing after adding the bridge edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_union_of_bridge_setup__p2m_6b761602_ec4e_4b71_82d8_bcea18a590f0_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hdata : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
      (bridge : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧
        arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc (0 : ℝ) 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by sorry
