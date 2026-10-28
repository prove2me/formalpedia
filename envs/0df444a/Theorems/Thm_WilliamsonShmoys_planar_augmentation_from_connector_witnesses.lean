-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_from_connector_witnesses
-- name    : WilliamsonShmoys.planar_augmentation_from_connector_witnesses
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:24:28.692742+00:00
-- url     : https://prove2.me/theorems/2a5597bc-3a87-40f0-a8f7-36db3721f55b
-- title:
--   Insert an edge from explicit connector witnesses
-- statement:
--   From the original drawing and the explicit connector witnesses, form the graph whose edge set is the old edge set with the unordered pair `{u,v}` inserted. Prove the inserted pair was not already an edge, preserve every old adjacency, and use the connector curve as the new edge arc. The proof is a drawing-to-graph construction and bookkeeping step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_from_connector_witnesses
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v)
    (hgeom : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (c : ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ x y, x < y → H.Adj x y →
        ContinuousOn (arc x y) (Set.Icc 0 1) ∧
        Set.InjOn (arc x y) (Set.Icc 0 1) ∧
        arc x y 0 = p x ∧ arc x y 1 = p y ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧
      (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b →
        (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (ContinuousOn c (Set.Icc 0 1) ∧
        Set.InjOn c (Set.Icc 0 1) ∧
        c 0 = p (min u v) ∧ c 1 = p (max u v) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, c t ≠ p w) ∧
        (∀ x y, x < y → H.Adj x y →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            c t = arc x y s →
              ∃ w, (w = min u v ∨ w = max u v) ∧ (w = x ∨ w = y) ∧
                ((t = 0 ∧ w = min u v) ∨ (t = 1 ∧ w = max u v)) ∧
                ((s = 0 ∧ w = x) ∨ (s = 1 ∧ w = y))))) :
    ∃ K : SimpleGraph V,
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
