-- Prove2me | Theorems.Thm_insert_edge_component_cardinality__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a4
-- name    : insert_edge_component_cardinality__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:54.800529+00:00
-- url     : https://prove2.me/theorems/15a3fa02-cdca-4efa-b2f2-07be25cf0531
-- title:
--   Component count after inserting an edge between components
-- statement:
--   Adding the edge identifies the old components of `u` and `v` and preserves every other component. Thus the new components correspond bijectively to the old components excluding the one containing `v`. A proof route is to map old quotient classes into the new reachability quotient, then prove injectivity on the restricted subtype and surjectivity using the merger of the endpoint classes.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

theorem insert_edge_component_cardinality__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a4
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (u v : V) (hne : u ≠ v) (hnreach : ¬ K.Reachable u v) :
    Nat.card {D : K.ConnectedComponent // D ≠ K.connectedComponentMk v} =
      Nat.card (K ⊔ SimpleGraph.edge u v).ConnectedComponent := by sorry
