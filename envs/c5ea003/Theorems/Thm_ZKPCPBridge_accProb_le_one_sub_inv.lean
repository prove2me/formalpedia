-- Prove2me | Theorems.Thm_ZKPCPBridge_accProb_le_one_sub_inv
-- name    : ZKPCPBridge.accProb_le_one_sub_inv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:53:45.349288+00:00
-- url     : https://prove2.me/theorems/61782edf-2a26-4e33-916d-0ab324a46aec
-- title:
--   The PCP gap: on a non-3-colorable instance every proof string is rejected with
-- statement:
--   **The PCP gap**: on a non-3-colorable instance every proof string is rejected with
--   probability at least `1/|E|`.
--
--   ```lean
--   theorem ZKPCPBridge.accProb_le_one_sub_inv[DecidableEq V] {E : Finset (V × V)} (hE : E.Nonempty)
--       (h : ¬ ThreeColorable E) (f : V → Fin 3) : accProb E f ≤ 1 - 1 / E.card := by sorry
--   /-! ## Exact parallel repetition -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ZeroKnowledge/PCPBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ZeroKnowledge/PCPBridge.lean#L105

-- Thm stub generated from Shared/ZeroKnowledge/PCPBridge.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_PCPBridge

/-!
# Bridge to probabilistically checkable proofs: 3-colorability as a 2-query PCP

The zero-knowledge protocol for graph 3-colorability is, stripped of its commitments,
exactly a *probabilistically checkable proof*: the proof string is a colouring
`f : V → Fin 3`, the verifier tosses `log₂ |E|` coins to pick an edge and reads only the
**two** proof symbols at its endpoints. This file makes that verifier and its parameters
precise and proves the completeness/soundness gap together with an exact parallel
repetition theorem.

## Main results

* `card_queries_le_two` — the verifier reads at most two proof symbols per test.
* `accepts_of_agree_on_queries` — *locality*: the verdict depends only on the queried
  symbols, so the verifier really is a 2-query oracle machine.
* `accProb_eq_one_iff` — perfect completeness, and its exact converse.
* `accProb_le_one_sub_inv` — the PCP gap: non-3-colorable instances are accepted with
  probability at most `1 - 1/|E|`.
* `prodAccept_card` — **exact parallel repetition**: the number of accepting `k`-tuples of
  tests is the `k`-th power of the number of accepting tests, hence
  `prodAccProb_eq_pow : (accepting k-tuples)/(all k-tuples) = accProb ^ k`.
* `prod_queries_card_le` and `prod_soundness_exp` — `k` repetitions use at most `2k`
  queries and drive the soundness error down to `exp (-k/|E|)`; taking `k = |E| · t`
  gives error `exp (-t)` (`prod_soundness_scaled`). This is the query-complexity /
  soundness trade-off underlying the PCP view of this verifier.
-/

open Finset

open ZKPCPBridge

variable {V : Type*}

/-! ## The two-query verifier -/

theorem ZKPCPBridge.accProb_le_one_sub_inv[DecidableEq V] {E : Finset (V × V)} (hE : E.Nonempty)
    (h : ¬ ThreeColorable E) (f : V → Fin 3) : accProb E f ≤ 1 - 1 / E.card := by sorry
