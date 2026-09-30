-- Prove2me | Theorems.Thm_Hirsch_gale_even_gap_exchange_routes
-- name    : Hirsch.gale_even_gap_exchange_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-18T23:48:23.228745+00:00
-- url     : https://prove2.me/theorems/1c79c95a-8107-4b7d-a81d-c1d120448924
-- title:
--   Construct bounded selected-set exchanges directly from Gale even gaps
-- statement:
--   For any natural m,d and two selected sets S,T of Fin m labels, each of cardinality d and satisfying the literal Gale even-gap condition (an even number of selected labels strictly between any two unselected labels), construct a walk of at most 2*(m-d)+1 nontrivial one-label exchanges from S to T. Every intermediate selected set has cardinality d and the same even-gap property. The complements are enumerated in increasing order, their indexed alternating parity is derived, and the accepted alternating-complement route is transported back to Fin m labels without identifying out-of-range naturals modulo m. No supplied complement enumeration, parity phase, graph, admissible intermediate sequence or bounded path is assumed. Empty/full universes, d=0,d=m, and equal endpoints are included. This is an order-only finite-set bridge; numerical root-polynomial equivalence and original exposed-edge transport remain separate geometric work. No shortestness, nonrevisiting, target locking, monotone score or unrestricted Polynomial Hirsch conclusion is claimed.
-- source:
--   Reuses the accepted #306 proof Hirsch.alternating_complement_exchange_routes (theorem640da3d5-6767-4a08-bdbc-70be357466af, proofba1b6db2200e659bfd2970ca635da800a3dd0d51) unchanged except its standalone root name and omitted old printouts. New work proves the rank-balance identity, both directions of even-gap/alternating-complement equivalence, finite-label enumeration and selected-set route transport. The finite-set predicate is literally that of the separately owned #302, whose unaccepted numerical proof is NOT imported. Classical Gale-evenness/packing mathematics is credited; no historical-priority claim.

import Mathlib
set_option autoImplicit false

theorem Hirsch.gale_even_gap_exchange_routes (m d : ℕ) (S T : Finset (Fin m))
    (hS : S.card = d) (hT : T.card = d)
    (hGS : ∀ i ∉ S, ∀ j ∉ S, i < j →
      (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0)
    (hGT : ∀ i ∉ T, ∀ j ∉ T, i < j →
      (T.filter (fun s => i < s ∧ s < j)).card % 2 = 0) :
    ∃ L : ℕ, L ≤ 2*(m-d)+1 ∧ ∃ p : ℕ → Finset (Fin m),
      p 0 = S ∧ p L = T ∧
      (∀ t, t ≤ L → (p t).card = d ∧
        ∀ i ∉ p t, ∀ j ∉ p t, i < j →
          ((p t).filter (fun s => i < s ∧ s < j)).card % 2 = 0) ∧
      ∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = d := by sorry
