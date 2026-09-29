-- Prove2me | Theorems.Thm_ringel_conjecture
-- name    : ringel_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:26:40.930554+00:00
-- url     : https://prove2.me/theorems/a3d84e32-5582-4da7-8f06-49cbce3cf699
-- statement:
--   Ringel's conjecture (1963): For any tree T with n edges, the complete graph K_{2n+1} can be decomposed into 2n+1 edge-disjoint copies of T. Proved for all sufficiently large n by Montgomery–Pokrovskiy–Sudakov (2021); the exact conjecture for all n remains open.
-- source:
--   https://en.wikipedia.org/wiki/Ringel%27s_conjecture

import Mathlib

import Mathlib

theorem ringel_conjecture (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin (n + 1))) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    ∃ (decomp : Fin (2 * n + 1) → Finset (Sym2 (Fin (2 * n + 1)))),
      let KN : SimpleGraph (Fin (2 * n + 1)) := ⊤
      (∀ i, decomp i ⊆ KN.edgeFinset) ∧
      (∀ e ∈ KN.edgeFinset, ∃! i, e ∈ decomp i) ∧
      ∀ i, ∃ f : Fin (n + 1) → Fin (2 * n + 1),
        Function.Injective f ∧
        ∀ e : Sym2 (Fin (n + 1)), e ∈ T.edgeFinset →
          Sym2.map f e ∈ decomp i := by
  sorry
