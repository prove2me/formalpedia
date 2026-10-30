-- Prove2me | Theorems.Thm_WilliamsonShmoys_insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
-- name    : WilliamsonShmoys.insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:15.908776+00:00
-- url     : https://prove2.me/theorems/bee5e24f-cd5c-4379-8d98-415a22bc9c47
-- title:
--   An avoiding arc extends a planar drawing
-- statement:
--   Given a planar drawing witness and a simple joining arc whose interior avoids every vertex and existing edge arc, construct a planar drawing of a supergraph that adds the edge between the designated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.insert_edge_along_avoiding_arc__p2m_28a8d91f_acdb_4d70_bde6_d0e0f7e29c29_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p ∧ (∀ x y, x < y → H.Adj x y → ContinuousOn (arc x y) (Set.Icc 0 1) ∧ Set.InjOn (arc x y) (Set.Icc 0 1) ∧ arc x y 0 = p x ∧ arc x y 1 = p y ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc x y t ≠ p w) ∧ (∀ x y a b, x < y → a < b → H.Adj x y → H.Adj a b → (x, y) ≠ (a, b) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, arc x y t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) (u v : V) (gamma : ℝ → ℝ × ℝ) (huv : u < v) (hnot : ¬ H.Adj u v) (hgamma : ContinuousOn gamma (Set.Icc 0 1) ∧ Set.InjOn gamma (Set.Icc 0 1) ∧ gamma 0 = p u ∧ gamma 1 = p v ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w) ∧ (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → H.Adj x y → ∀ s ∈ Set.Icc (0 : ℝ) 1, gamma t ≠ arc x y s)) : ∃ G : SimpleGraph V, H ≤ G ∧ ∃ a b : V, a ≠ b ∧ ¬ H.Adj a b ∧ G.Adj a b ∧ HasPlanarDrawingOn G := by sorry
