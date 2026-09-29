-- Prove2me | Theorems.Thm_lovasz_hamiltonian_conjecture
-- name    : lovasz_hamiltonian_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:49:20.103378+00:00
-- url     : https://prove2.me/theorems/496e23ca-1251-431c-a535-cf3a23d332ce
-- statement:
--   Lovász conjecture (1969): Every finite connected vertex-transitive graph has a Hamiltonian path (a simple path through all vertices). Known for Cayley graphs of abelian groups; the general case is open.
-- source:
--   https://en.wikipedia.org/wiki/Lov%C3%A1sz_conjecture

import Mathlib

import Mathlib

-- Lovász conjecture: every connected vertex-transitive graph has a Hamiltonian path
theorem lovasz_hamiltonian_conjecture (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (htrans : ∀ u v : V, ∃ φ : V ≃ V,
      φ u = v ∧ ∀ a b : V, G.Adj a b ↔ G.Adj (φ a) (φ b)) :
    ∃ path : List V, path.Nodup ∧
      path.length = Fintype.card V ∧
      List.Chain' G.Adj path := by
  sorry
