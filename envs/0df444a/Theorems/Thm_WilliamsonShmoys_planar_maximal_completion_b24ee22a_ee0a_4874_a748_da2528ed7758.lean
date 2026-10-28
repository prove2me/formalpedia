-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_completion_b24ee22a_ee0a_4874_a748_da2528ed7758
-- name    : WilliamsonShmoys.planar_maximal_completion_b24ee22a_ee0a_4874_a748_da2528ed7758
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:09:00.298067+00:00
-- url     : https://prove2.me/theorems/178de207-bc38-49c9-a36b-bed216498e33
-- title:
--   Inclusion-maximal drawable completion on the fixed vertex set
-- statement:
--   A drawable graph on a finite vertex type has a drawable supergraph on that same type that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_completion_b24ee22a_ee0a_4874_a748_da2528ed7758
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
