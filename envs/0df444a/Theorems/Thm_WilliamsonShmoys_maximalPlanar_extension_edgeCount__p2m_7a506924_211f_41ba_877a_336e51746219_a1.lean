-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1
-- name    : WilliamsonShmoys.maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:46.599601+00:00
-- url     : https://prove2.me/theorems/6cde29f9-0337-48f4-829a-b67e3b72f2a9
-- title:
--   Planar extension with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. This packages the planar edge-extension and Euler-counting argument; the parent then uses maximality to show the extension has the same edge set as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1 {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧ U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
