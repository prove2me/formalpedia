-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
-- name    : WilliamsonShmoys.planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:35.136847+00:00
-- url     : https://prove2.me/theorems/d0f89697-37ff-451e-845a-636f1ada035f
-- title:
--   Local validity of the augmented bridge arc
-- statement:
--   For each ordered edge of the union graph, the explicitly written augmented arc is continuous and injective on the unit interval, has the correct endpoints, and avoids all vertex locations in the open interval.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_bridge_augmented_arc_local__p2m_3ac38dfe_f4e4_4970_8b72_a722a3a2a331_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (bridge : ℝ → ℝ × ℝ)
    (hne : u ≠ v) (hnew : ¬ H.Adj u v)
    (hdraw : Function.Injective p ∧
      (∀ a b, a < b → H.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
        (a, b) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hbridge : ContinuousOn bridge (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn bridge (Set.Icc 0 1) ∧ bridge 0 = p u ∧ bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    ∀ a b, a < b →
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))).Adj a b →
      ContinuousOn
        ((fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b)
        (Set.Icc 0 1) ∧
      Set.InjOn
        ((fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b)
        (Set.Icc 0 1) ∧
      (fun a b t => if u < v then
        if a = u ∧ b = v then bridge t else arc a b t
      else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b 0 = p a ∧
      (fun a b t => if u < v then
        if a = u ∧ b = v then bridge t else arc a b t
      else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w,
        (fun a b t => if u < v then
          if a = u ∧ b = v then bridge t else arc a b t
        else if a = v ∧ b = u then bridge (1 - t) else arc a b t) a b t ≠ p w := by sorry
