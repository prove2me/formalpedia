-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_by_finite_edges
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_by_finite_edges
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:22:44.777431+00:00
-- url     : https://prove2.me/theorems/05abea6d-e8f9-47ba-a08b-133f543e103e
-- title:
--   A drawable supergraph maximal by inclusion
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal by inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_by_finite_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
