-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
-- name    : WilliamsonShmoys.planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:12.022321+00:00
-- url     : https://prove2.me/theorems/bf289d32-cca7-4333-88c2-c2fcc6d37024
-- title:
--   Preserve a planar drawing when the added edge already exists
-- statement:
--   If the given drawing and bridge data hold and H already contains the edge between the distinct vertices u and v, then adding that singleton edge by graph union preserves the planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_union_existing_edge__p2m_8e7db580_fca5_4354_8e58_39b297c20583_a1
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
      Set.InjOn bridge (Set.Icc 0 1) ∧
      bridge 0 = p u ∧
      bridge 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, bridge t ≠ p w) ∧
      (∀ a b, a < b → H.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          bridge t = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)))
    (hne : u ≠ v) (hedge : H.Adj u v) :
    HasPlanarDrawingOn
      (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by sorry
