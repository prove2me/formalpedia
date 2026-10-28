-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_planar_drawing
-- name    : WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:23:43.890255+00:00
-- url     : https://prove2.me/theorems/9b2ff300-6bba-4085-aab5-671a57fc3635
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   A graph maximal among same-vertex drawable supergraphs has exactly 3n − 6 edges when its finite vertex set has size n ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    L.edgeSet.ncard = 3 * n - 6 := by sorry
