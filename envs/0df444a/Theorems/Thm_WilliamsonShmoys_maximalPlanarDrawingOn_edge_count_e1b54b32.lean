-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_e1b54b32
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_e1b54b32
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:24:08.239882+00:00
-- url     : https://prove2.me/theorems/64cb9f36-4aba-44dd-8780-0c68ad33fc76
-- title:
--   An edge-maximal planar drawing has the triangulation edge count
-- statement:
--   A planar simple graph on at least three vertices with no strictly larger planar supergraph has exactly three times its vertex count minus six edges. The argument converts the arc drawing into planar embedding structure, proves edge-maximality forces triangular faces, and applies Euler’s formula. This child contains the remaining geometric and Euler-formula obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_e1b54b32
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      N.edgeSet ⊂ P.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn P) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
