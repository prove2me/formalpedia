-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_retry2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:29:05.782382+00:00
-- url     : https://prove2.me/theorems/4c1a785c-cbf1-4dc5-845b-5e8e36fd9c50
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Any finite graph with a planar drawing has a supergraph on the same vertex type that also has a planar drawing and is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      forall N : SimpleGraph V, M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M := by sorry
