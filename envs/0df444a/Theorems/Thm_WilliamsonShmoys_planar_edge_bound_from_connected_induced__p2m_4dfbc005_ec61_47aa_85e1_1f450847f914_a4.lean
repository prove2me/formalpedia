-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- name    : WilliamsonShmoys.planar_edge_bound_from_connected_induced__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:13.286105+00:00
-- url     : https://prove2.me/theorems/dfaa3708-38f1-460c-bec8-c36da50b4703
-- title:
--   Combine bounds on connected induced subgraphs
-- statement:
--   If every connected induced subgraph with at least three vertices satisfies the Euler edge bound, then the whole graph does too, including when it is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_connected_induced__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hcomp : ∀ (s : Set V) [Fintype {x // x ∈ s}],
      3 ≤ s.ncard → (M.induce s).Connected →
      (M.induce s).edgeSet.ncard + 6 ≤ 3 * s.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
