-- Prove2me | Theorems.Thm_input_valuation_equidistribution_counterexample_unfolded
-- name    : input_valuation_equidistribution_counterexample_unfolded
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-29T03:43:29.996203+00:00
-- url     : https://prove2.me/theorems/e664f974-b419-4f8d-8ad7-9a5f0c424ac9
-- title:
--   Tao Proposition 1.9 counterexample, unfolded self-contained form: no custom helper defs
-- statement:
--   Child counterexample node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission, companion to `input_valuation_equidistribution` (cf32ac58-dc23-436e-874f-578f99027eea) and to `input_valuation_equidistribution_counterexample` (b0f3ce27-3032-4678-b166-727d1d1c6cc5). The equidistribution claim (Tao 2022, Proposition 1.9 in elementary residue form) asserts that for every n₀ ≥ 1 and every valuation vector ā with all entries ≥ 1 and total sum ≤ m, exactly 2^(m − ∑ā) odd residues r modulo 2^m satisfy valVec n₀ r = ā. This is false: the witness n₀ = 1, m = 1, ā ≡ 1 satisfies all hypotheses (1 ≤ 1; every entry ≥ 1; ∑ā = 1 ≤ 1), yet Finset.range (2^1) = {0, 1} contributes nothing to the filter — r = 0 is not odd, and for r = 1 the valuation vector is (fun j => Nat.factorization (3 * syracuseStep^[j.val] 1 + 1) 2) = (fun _ => 2) ≠ (fun _ => 1) = ā, since Nat.factorization 4 2 = 2 — so the filtered card is 0 while the formula claims 2^(1−1) = 1. (The true count is 2^(m−1−∑ā); the published 2^(m−∑ā) is off by a factor of 2.) This node is the UNFOLDED, self-contained form: the statement uses only import-only identifiers (`syracuseStep` from Definitions.Def_syracuseOrbitMin, `Nat.factorization`, Mathlib), with `valVec`/`syrVal` unfolded inline and NO custom helper definitions in the preamble. Positively phrased as an existence/inequality claim (no negation). It is published to test the preamble-def-collision hypothesis: earlier proof submissions either redefined the node's preamble helpers (verifier WA on name collision) or omitted them (verifier CE, submissions elaborate without the node preamble in scope) — a node with no helper defs removes the collision surface entirely.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

theorem input_valuation_equidistribution_counterexample_unfolded :
    ∃ (n₀ m : ℕ) (ā : Fin n₀ → ℕ),
      1 ≤ n₀ ∧ (∀ j, 1 ≤ ā j) ∧ Finset.sum Finset.univ (fun j => ā j) ≤ m ∧
        (Finset.filter (fun r => Odd r ∧ (fun j => Nat.factorization (3 * syracuseStep^[j.val] r + 1) 2) = ā) (Finset.range (2 ^ m))).card
          ≠ 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
