-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_of_safe_bridge
-- name    : WilliamsonShmoys.extend_of_safe_bridge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:11:12.237591+00:00
-- url     : https://prove2.me/theorems/1d9314e3-6c8b-411f-a63d-c02ea42ea559
-- title:
--   Assemble a planar extension from a safe bridge
-- statement:
--   Given a safe bridge, add its endpoint pair as one edge and use its arc for that pair while retaining every old arc. This yields the graph inclusion, reachability condition, new disconnected-component edge, and drawing properties in the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_HasSafeBridge

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.extend_of_safe_bridge
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
    (hBridge : WilliamsonShmoys.HasSafeBridge G p arc) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      (∃ u v, H.Adj u v ∧ ¬ G.Reachable u v) ∧
      ∃ arc' : V → V → ℝ → ℝ × ℝ,
        (∀ u v, u < v → G.Adj u v → arc' u v = arc u v) ∧
        (∀ u v, u < v → H.Adj u v →
          ContinuousOn (arc' u v) (Set.Icc 0 1) ∧
          Set.InjOn (arc' u v) (Set.Icc 0 1) ∧
          arc' u v 0 = p u ∧
          arc' u v 1 = p v ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc' u v t ≠ p w) ∧
        (∀ u v x y, u < v → x < y → H.Adj u v → H.Adj x y →
          (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
            arc' u v t = arc' x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by sorry
