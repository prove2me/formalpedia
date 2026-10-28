-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_cut_separates_reachable
-- name    : WilliamsonShmoys.planar_cut_separates_reachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:41:18.301881+00:00
-- url     : https://prove2.me/theorems/654fd08c-bb89-4d5b-ba09-0c8aa3209c30
-- title:
--   An edge-free cut separates reachable vertices
-- statement:
--   If no edge crosses a vertex cut, then vertices on opposite sides cannot be joined by a path. This removes the cut-specific graph argument from the parent and supplies the disconnectedness hypothesis for the geometric bridge lemma. Prove it by induction along a path from u: every next vertex remains in A by the cut condition, contradicting that the path ends at v outside A. The boundary cases are covered by hu and hv; no planarity assumptions are needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_cut_separates_reachable
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (A : Set V)
    (hCut : ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y)
    (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    ¬ K.Reachable u v := by sorry
