-- Prove2me | Theorems.Thm_WilliamsonShmoys_reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- name    : WilliamsonShmoys.reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:50.580452+00:00
-- url     : https://prove2.me/theorems/35f51d82-37d1-47f6-9113-8cd44ef7b772
-- title:
--   Reachability component separates disconnected vertices
-- statement:
--   If `v` is not reachable from `u`, the vertices reachable from `u` form a separating set containing `u` and excluding `v`, with no edge crossing to its complement. The independent proof route is to take `A := {w | G.Reachable u w}` and use reachability closure under adjacency to rule out a crossing edge. This removes the graph connectivity argument from the parent; it leaves only the geometric redrawing operation in the second child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V)
    (hdisconnected : ¬ G.Reachable u v) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧
      ∀ a b, a ∈ A → b ∉ A → ¬ G.Adj a b := by sorry
