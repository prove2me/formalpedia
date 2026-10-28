-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_completion_exact_edge_count
-- name    : WilliamsonShmoys.exists_planar_completion_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:14:56.358998+00:00
-- url     : https://prove2.me/theorems/a3bf2761-3b00-45d2-af0e-a4c0f6d1919f
-- title:
--   Every finite drawable graph has a triangulated completion
-- statement:
--   Any finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_completion_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
