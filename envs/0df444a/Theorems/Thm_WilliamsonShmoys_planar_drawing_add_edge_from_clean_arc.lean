-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_from_clean_arc
-- name    : WilliamsonShmoys.planar_drawing_add_edge_from_clean_arc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:57:04.095037+00:00
-- url     : https://prove2.me/theorems/64704fae-0f21-4cfe-9e52-452b6e63d75a
-- title:
--   Add a clean arc to a planar drawing
-- statement:
--   Given the drawing data and a clean arc between the ordered unreachable vertices, form a strict supergraph containing the new edge and its planar drawing. The proof adds the symmetric adjacency pair, uses γ for that pair, and retains the old arcs for other edges. The endpoint and intersection clauses establish the drawing conditions, while non-reachability establishes strictness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_from_clean_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    {u v : V}
    (huv : u < v)
    (hUnreachable : ¬ G.Reachable u v)
    (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (γ : ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdges : ∀ x y, x < y → G.Adj x y →
      ContinuousOn (arc x y) (Set.Icc 0 1) ∧
      Set.InjOn (arc x y) (Set.Icc 0 1) ∧
      arc x y 0 = p x ∧ arc x y 1 = p y ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w)
    (hCross : ∀ x y a b, x < y → a < b → G.Adj x y → G.Adj a b →
      (x, y) ≠ (a, b) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        arc x y t = arc a b s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (hγContinuous : ContinuousOn γ (Set.Icc 0 1))
    (hγInjective : Set.InjOn γ (Set.Icc 0 1))
    (hγStart : γ 0 = p u)
    (hγEnd : γ 1 = p v)
    (hγAvoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hγCross : ∀ x y, x < y → G.Adj x y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        γ t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
