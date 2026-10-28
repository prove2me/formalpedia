-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exists_20261026
-- name    : WilliamsonShmoys.planar_extension_exists_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:43:58.017676+00:00
-- url     : https://prove2.me/theorems/4c8b4fb0-e9bd-4184-972a-6e2107676f86
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   A planar graph on a finite fixed vertex set is contained in a planar supergraph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_exists_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        ∀ L : SimpleGraph V, J ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = J := by sorry
