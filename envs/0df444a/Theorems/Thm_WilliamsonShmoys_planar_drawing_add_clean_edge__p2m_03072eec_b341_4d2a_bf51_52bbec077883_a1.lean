-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- name    : WilliamsonShmoys.planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:44.146978+00:00
-- url     : https://prove2.me/theorems/a28e5ee4-bf60-4e7a-aa04-8ab47cd06895
-- title:
--   Adding an edge along a clean joining arc
-- statement:
--   If a simple arc joins two nonadjacent vertices and its interior misses all vertices and existing edge arcs, adding that edge yields a strict edge supergraph with a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_clean_edge__p2m_03072eec_b341_4d2a_bf51_52bbec077883_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hdrawing : ∀ u v, u < v → K.Adj u v →
      ContinuousOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (arc u v) (Set.Icc (0 : ℝ) 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hcross : ∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
        (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (gamma : ℝ → ℝ × ℝ)
    (huv : u < v) (hnonadj : ¬ K.Adj u v)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn gamma (Set.Icc (0 : ℝ) 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (harcs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → K.Adj x y →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K.edgeFinset ⊂ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
