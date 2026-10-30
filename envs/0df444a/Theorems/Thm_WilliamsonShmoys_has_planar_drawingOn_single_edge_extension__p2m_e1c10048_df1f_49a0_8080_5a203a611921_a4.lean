-- Prove2me | Theorems.Thm_WilliamsonShmoys_has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
-- name    : WilliamsonShmoys.has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:44.440244+00:00
-- url     : https://prove2.me/theorems/0a30e766-e49d-4d84-80e9-e4eabe247279
-- title:
--   Extend a planar drawing across one certified edge
-- statement:
--   Given a drawing of `H`, a certified simple arc from `u` to `v`, and a graph `K` whose ordered adjacencies are exactly those of `H` plus `(u,v)`, construct a planar drawing of `K`. Retain the old arc if the edge already belongs to `H`; otherwise use the supplied arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.has_planar_drawingOn_single_edge_extension__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ a b, a < b → H.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → H.Adj a b → H.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc a b t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (c : ℝ → ℝ × ℝ)
    (huv : u < v)
    (hccont : ContinuousOn c (Set.Icc 0 1))
    (hcinj : Set.InjOn c (Set.Icc 0 1))
    (hc0 : c 0 = p u)
    (hc1 : c 1 = p v)
    (hcvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w)
    (hccross : ∀ x y, x < y → H.Adj x y → (u, v) ≠ (x, y) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        c t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hAdj : ∀ a b, a < b →
      (K.Adj a b ↔ H.Adj a b ∨ (a = u ∧ b = v))) :
    HasPlanarDrawingOn K := by sorry
