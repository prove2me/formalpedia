-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion_finite_maximal_extension_553ae5ef
-- name    : WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_finite_maximal_extension_553ae5ef
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:27:10.532013+00:00
-- url     : https://prove2.me/theorems/03e3b9f8-a28e-47b0-bf49-ca9b65e33c25
-- title:
--   A drawable graph has a finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. The graph universe is finite, and the original graph makes the family of drawable supergraphs nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_finite_maximal_extension_553ae5ef
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V,
          K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
