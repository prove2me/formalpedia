-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_b74a49f4
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_b74a49f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:42:43.095738+00:00
-- url     : https://prove2.me/theorems/ef36ba6e-5efb-499c-82d0-8b1f07770eb5
-- title:
--   Inclusion-maximal planar supergraph on a finite vertex type
-- statement:
--   Every graph with the stated planar drawing on a finite ordered vertex type is contained in an inclusion-maximal planar simple graph on that same vertex type. The route is to maximize edge-set cardinality over the finite collection of planar supergraphs containing the input; any proper extension would strictly increase the cardinality. This statement needs no lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
