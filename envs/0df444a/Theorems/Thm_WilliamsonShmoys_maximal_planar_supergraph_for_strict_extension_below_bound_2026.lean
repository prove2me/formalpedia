-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_for_strict_extension_below_bound_2026
-- name    : WilliamsonShmoys.maximal_planar_supergraph_for_strict_extension_below_bound_2026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:41:45.086373+00:00
-- url     : https://prove2.me/theorems/993ee2c1-34d6-42c4-a098-920387fce6ce
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. Choose a drawable supergraph maximizing the number of edges among the finite family of supergraphs of `L` that admit a drawing; any strict drawable extension would have more edges. This removes the maximal-extension selection step from the parent and needs no lower bound on the number of vertices. It is independently proved by finite maximization and the fact that strict inclusion between finite edge sets increases cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_for_strict_extension_below_bound_2026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K := by sorry
