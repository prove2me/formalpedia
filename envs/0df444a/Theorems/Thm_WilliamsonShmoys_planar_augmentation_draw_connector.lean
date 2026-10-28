-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_draw_connector
-- name    : WilliamsonShmoys.planar_augmentation_draw_connector
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:47:16.530737+00:00
-- url     : https://prove2.me/theorems/b6e9852b-a84c-42be-bce1-246d4e172599
-- title:
--   Extend a planar drawing using connector witnesses
-- statement:
--   Extend the supplied drawing of `H` to the graph with `{u,v}` inserted, using `c` as the new edge curve and the connector hypotheses to establish the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_draw_connector
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v)
    (hgeom : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (c : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧ Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (ContinuousOn c (Set.Icc 0 1) ∧ Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p (min u v) ∧ c 1 = p (max u v) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, c t = arc x y s →
            ∃ w, (w = min u v ∨ w = max u v) ∧ (w = x ∨ w = y) ∧
              ((t = 0 ∧ w = min u v) ∨ (t = 1 ∧ w = max u v)) ∧
              ((s = 0 ∧ w = x) ∨ (s = 1 ∧ w = y))))) :
    WilliamsonShmoys.HasPlanarDrawingOn
      (SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet)) := by
  sorry
