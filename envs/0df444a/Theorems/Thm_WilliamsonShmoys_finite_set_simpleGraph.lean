-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_set_simpleGraph
-- name    : WilliamsonShmoys.finite_set_simpleGraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:53:26.340298+00:00
-- url     : https://prove2.me/theorems/4abd3662-e904-404d-8709-22d2b224d4ce
-- title:
--   Finite family of simple graphs on a finite vertex type
-- statement:
--   Every set of simple graphs on a finite vertex type is finite. This supplies finiteness of the drawable-supergraph candidate set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_set_simpleGraph
    {V : Type} [Fintype V] (s : Set (SimpleGraph V)) :
    s.Finite := by sorry
