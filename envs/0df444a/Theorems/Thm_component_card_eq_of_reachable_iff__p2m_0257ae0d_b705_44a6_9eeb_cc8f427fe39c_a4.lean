-- Prove2me | Theorems.Thm_component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4
-- name    : component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:35.730367+00:00
-- url     : https://prove2.me/theorems/356eb727-82ad-4ae3-931b-e20f1afcc334
-- title:
--   Reachability equivalence preserves component cardinality
-- statement:
--   Graphs on the same vertex type with equivalent reachability relations have equally many connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open SimpleGraph

theorem component_card_eq_of_reachable_iff__p2m_0257ae0d_b705_44a6_9eeb_cc8f427fe39c_a4
    {V : Type} (F K : SimpleGraph V)
    (hReach : ∀ u v, F.Reachable u v ↔ K.Reachable u v) :
    Nat.card F.ConnectedComponent = Nat.card K.ConnectedComponent := by sorry
