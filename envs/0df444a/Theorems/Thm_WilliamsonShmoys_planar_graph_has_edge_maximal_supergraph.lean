-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_maximal_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:44:59.72287+00:00
-- url     : https://prove2.me/theorems/8ec9f968-2ea5-46cb-87b3-7f9beb075084
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every planar graph on a finite linearly ordered vertex type has a planar supergraph on the same vertices that has no strictly larger planar supergraph. This removes the finite maximization step from the parent theorem. An independent route is to maximize the edge set among the finitely many simple graphs containing X that satisfy the drawing predicate; X itself ensures the candidate set is nonempty. Drawing inheritance under edge deletion preserves planarity when comparing candidates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X) :
    exists Y : SimpleGraph V,
      HasPlanarDrawingOn Y /\
      (forall u v, X.Adj u v -> Y.Adj u v) /\
      (forall Z : SimpleGraph V,
        HasPlanarDrawingOn Z ->
        (forall u v, Y.Adj u v -> Z.Adj u v) ->
        forall u v, Z.Adj u v -> Y.Adj u v) := by sorry
