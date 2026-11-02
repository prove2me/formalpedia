-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
-- name    : WilliamsonShmoys.planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:24.036203+00:00
-- url     : https://prove2.me/theorems/19cd2d46-2b88-4ae0-bdf6-b262bd78d159
-- title:
--   Split a planar graph across an unreachable component
-- statement:
--   Partition the edges of a planar graph into two planar graphs supported on opposite sides of a vertex set S, where u lies in S and v lies outside S, whenever u and v are unreachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_component_cut__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ S : Set V, ∃ A B : SimpleGraph V,
      u ∈ S ∧ v ∉ S ∧
      (∀ a b, G.Adj a b ↔ A.Adj a b ∨ B.Adj a b) ∧
      (∀ a b, A.Adj a b → a ∈ S ∧ b ∈ S) ∧
      (∀ a b, B.Adj a b → a ∉ S ∧ b ∉ S) ∧
      HasPlanarDrawingOn A ∧ HasPlanarDrawingOn B := by sorry
