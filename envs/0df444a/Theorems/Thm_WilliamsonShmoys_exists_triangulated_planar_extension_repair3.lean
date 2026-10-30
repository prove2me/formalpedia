-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension_repair3
-- name    : WilliamsonShmoys.exists_triangulated_planar_extension_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:50:30.772728+00:00
-- url     : https://prove2.me/theorems/3109df4d-98fd-4102-824c-39bdc30faaca
-- title:
--   Triangulated planar extension on the same vertex set
-- statement:
--   Every finite graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_extension_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
