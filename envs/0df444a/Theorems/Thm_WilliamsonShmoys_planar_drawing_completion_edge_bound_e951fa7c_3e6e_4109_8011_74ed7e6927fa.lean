-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:09:41.978281+00:00
-- url     : https://prove2.me/theorems/536dd7c5-55fb-48e9-82b0-863b2ebb607e
-- title:
--   Planar drawing completion gives an edge lower bound
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This isolates the topological completion and edge-counting work. Its proof must address disconnected drawings and isolated vertices before applying a face-count argument and Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ X : SimpleGraph V,
      LE.le W X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V - 6 <= X.edgeSet.ncard := by sorry
