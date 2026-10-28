-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_components_with_fixed_vertices
-- name    : WilliamsonShmoys.planar_drawing_extend_components_with_fixed_vertices
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T09:32:10.068968+00:00
-- url     : https://prove2.me/theorems/cb7f9034-39b5-414b-9d8a-1a3d66651d0a
-- title:
--   Extend a disconnected planar drawing while fixing its vertices
-- statement:
--   Given a finite disconnected graph and a drawing satisfying the supplied arc conditions, extend the graph and its edge arcs while keeping every vertex at its original point and preserving the original arcs. The extended drawing remains planar, and at least one added edge joins originally unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extend_components_with_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdgeDrawing : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧
      arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hNoCrossing : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hGdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) ∧
      ∃ arc' : V → V → ℝ → ℝ × ℝ,
        (∀ u v, u < v → H.Adj u v →
          ContinuousOn (arc' u v) (Set.Icc 0 1) ∧
          Set.InjOn (arc' u v) (Set.Icc 0 1) ∧
          arc' u v 0 = p u ∧
          arc' u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc' u v t ≠ p w) ∧
        (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            arc' u v t = arc' x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  sorry
