-- Prove2me | Theorems.Thm_erdos_szekeres_asymmetric_graph_bound
-- name    : erdos_szekeres_asymmetric_graph_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T09:49:13.057996+00:00
-- url     : https://prove2.me/theorems/624b0a1c-3ea4-4245-803f-9d42fc1909f9
-- title:
--   Erdos-Szekeres asymmetric Ramsey bound for finite graphs
-- statement:
--   For positive integers k and l, every simple graph on binom(k+l-2,k-1) vertices contains either a clique of size k or an independent set of size l. This is the finite-graph form of the Erdos-Szekeres bound R(k,l) <= binom(k+l-2,k-1).
-- source:
--   P. Erdos and G. Szekeres, A combinatorial problem in geometry, Compositio Mathematica 2 (1935), pp. 463-470, https://www.numdam.org/item/CM_1935__2__463_0/

import Mathlib

theorem erdos_szekeres_asymmetric_graph_bound (k l : Nat) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∀ G : SimpleGraph (Fin (Nat.choose (k + l - 2) (k - 1))),
      (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), G.IsNClique k s) ∨
      (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), Gᶜ.IsNClique l s) := by sorry
