-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_extension_finite__p2m_8483dba4_46b0_4557_8588_2cfeb83216a6_a3
-- name    : WilliamsonShmoys.exists_maximal_graph_extension_finite__p2m_8483dba4_46b0_4557_8588_2cfeb83216a6_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:46.377683+00:00
-- url     : https://prove2.me/theorems/9f3e6a97-c623-4a15-9543-38a021dd3fb9
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   If a graph on a finite vertex type satisfies a graph predicate, it has a predicate-satisfying supergraph that is maximal under graph inclusion. The hypothesis that `H` satisfies `P` ensures the eligible family is nonempty, including for empty and singleton vertex types. The parent instantiates `P` with `HasPlanarDrawingOn`. A proof route is to choose an eligible graph with the largest edge set; a proper eligible extension must add an edge, contradicting that choice. Establishing this finite maximality argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_graph_extension_finite__p2m_8483dba4_46b0_4557_8588_2cfeb83216a6_a3
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V -> Prop)
    (hH : P H) :
    Exists fun K : SimpleGraph V => H <= K /\ P K /\
      forall K' : SimpleGraph V, K <= K' -> P K' -> K' = K := by sorry
