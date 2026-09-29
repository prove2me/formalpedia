-- Prove2me | Theorems.Thm_oberwolfach_problem
-- name    : oberwolfach_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T20:36:59.026572+00:00
-- url     : https://prove2.me/theorems/97346650-4283-4d7b-a7a9-0e511958850a
-- statement:
--   The Oberwolfach problem (Ringel 1967): Given k tables of sizes c₁,...,cₖ with c₁+...+cₖ = n (odd), can n people be seated at round tables so that everyone shares a table with everyone else exactly once over the (n-1)/2 sessions? Equivalent to decomposing Kₙ into 2-factors matching the table sizes. Solved for n ≤ 200 and many special cases; general case open.
-- source:
--   https://en.wikipedia.org/wiki/Oberwolfach_problem

import Mathlib

import Mathlib

theorem oberwolfach_problem (n : ℕ) (hn : 3 ≤ n) (hodd : ¬ 2 ∣ n)
    (k : ℕ) (cycles : Fin k → ℕ)
    (hlen : ∀ i, 3 ≤ cycles i)
    (hsum : ∑ i, cycles i = n) :
    ∃ (decomp : Fin ((n - 1) / 2) → Finset (Sym2 (Fin n))),
      let KN : SimpleGraph (Fin n) := ⊤
      (∀ r, decomp r ⊆ KN.edgeFinset) ∧
      (∀ e ∈ KN.edgeFinset, ∃! r, e ∈ decomp r) ∧
      ∀ r, ∃ f : Fin k → Finset (Sym2 (Fin n)),
        decomp r = Finset.biUnion Finset.univ f ∧
        ∀ i, (f i).card = cycles i := by
  sorry
