-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- name    : WilliamsonShmoys.planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:09:57.242797+00:00
-- url     : https://prove2.me/theorems/20c47d60-fca7-4a1b-b5c7-c8408502290b
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion implies that the first graph’s edge-set cardinality is at most the second’s. This removes the bookkeeping step transferring the completion bound to W; prove it from edge-set inclusion and finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : LE.le G H) :
    G.edgeSet.ncard <= H.edgeSet.ncard := by sorry
