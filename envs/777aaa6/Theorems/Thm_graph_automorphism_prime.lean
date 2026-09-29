-- Prove2me | Theorems.Thm_graph_automorphism_prime
-- name    : graph_automorphism_prime
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T02:34:10.686647+00:00
-- url     : https://prove2.me/theorems/28640283-d3d2-46b8-9d9f-29aa1ddaada1
-- statement:
--   Graph automorphism conjecture: For prime n, every automorphism of a connected n-vertex graph has order dividing n. Related to Cayley's theorem. Special cases proved; general conjecture open.
-- source:
--   https://en.wikipedia.org/wiki/Graph_automorphism

import Mathlib

import Mathlib

theorem graph_automorphism_prime (n : ℕ) (hn : 2 ≤ n) (hp : Nat.Prime n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    ∀ phi : Equiv.Perm (Fin n),
      (∀ v w : Fin n, G.Adj v w ↔ G.Adj (phi v) (phi w)) →
      phi ^ n = Equiv.refl (Fin n) := by
  sorry
