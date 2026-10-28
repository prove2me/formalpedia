-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_extension_maximizing_adjacencies
-- name    : WilliamsonShmoys.exists_drawable_extension_maximizing_adjacencies
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:58:48.292882+00:00
-- url     : https://prove2.me/theorems/c8455c91-d7d3-44bd-9bea-9e78c5104854
-- title:
--   A drawable extension maximizing adjacent pairs
-- statement:
--   Among drawable supergraphs of N, one maximizes the number of ordered adjacent vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_extension_maximizing_adjacencies
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      And (LE.le N K) (And (HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, LE.le N L -> HasPlanarDrawingOn L ->
          Nat.card {p : V × V // L.Adj p.1 p.2} <=
            Nat.card {p : V × V // K.Adj p.1 p.2})) := by sorry
