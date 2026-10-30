-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_cardinality_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_cardinality_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:45:43.197403+00:00
-- url     : https://prove2.me/theorems/f663d05c-99da-48e1-89c4-968325b370bc
-- title:
--   Maximal planar graphs have at least three times the vertex count minus six edges
-- statement:
--   An inclusion-maximal graph with the specified planar drawing on a finite ordered vertex type with at least three vertices has at least 3|V| − 6 edges. Maximality is among planar supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_cardinality_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      ∀ ⦃u v⦄, L.Adj u v → K.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
