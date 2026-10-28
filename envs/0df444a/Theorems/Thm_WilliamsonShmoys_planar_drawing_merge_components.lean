-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_merge_components
-- name    : WilliamsonShmoys.planar_drawing_merge_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:52:25.227081+00:00
-- url     : https://prove2.me/theorems/746d7574-5a7c-455b-b6b2-68643c73927d
-- title:
--   Planar drawing extension that merges components
-- statement:
--   A disconnected finite graph with the specified planar drawing has a planar supergraph on the same vertices that preserves its edges and makes strictly more ordered vertex pairs reachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_merge_components {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hplanar : HasPlanarDrawingOn H) (hnot : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      Nat.card {p : V × V // ¬ K.Reachable p.1 p.2} <
        Nat.card {p : V × V // ¬ H.Reachable p.1 p.2} := by sorry
