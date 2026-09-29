-- Prove2me | Theorems.Thm_fib_carmichael_composite
-- name    : fib_carmichael_composite
-- status  : Open
-- author  : @raver1975
-- created : 2026-09-08T15:54:33.078982+00:00
-- url     : https://prove2.me/theorems/c65f6248-ecfe-4494-9360-a0b37639be97
-- title:
--   Certified composite range of Carmichael's theorem.
-- statement:
--   **Certified composite range of Carmichael's theorem.** A composite index
--   `n` with `13 â¤ n â¤ 10000` has a primitive prime divisor of `F(n)`.
--
--   ```lean
--   theorem fib_carmichael_composite(n : ℕ) (hn : 13 ≤ n) (hn2 : n ≤ 10000)
--       (hnp : ¬Nat.Prime n) :
--       ∃ p, Nat.Prime p ∧ p ∣ Nat.fib n ∧
--         ∀ k, 0 < k → k < n → ¬(p ∣ Nat.fib k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/NumberTheory/CarmichaelProof.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/NumberTheory/CarmichaelProof.lean#L121

-- Thm stub generated from Shared/NumberTheory/CarmichaelProof.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_CarmichaelProof
-- [catalogfix] missing module: import Shared.NumberTheory.CarmichaelHelper

/-! # Certified finite range of Carmichael's theorem (composite case)

We prove that every composite `n` with `13 ≤ n ≤ 10000` gives `F(n)` a
primitive prime divisor.
-/

set_option maxHeartbeats 800000

/-! ## Bridge Lemma -/


/-! ## Computational verification infrastructure -/




/-! ## Correctness lemmas -/






/-! ## Computational verification -/


/-! ## The composite case -/

theorem fib_carmichael_composite(n : ℕ) (hn : 13 ≤ n) (hn2 : n ≤ 10000)
    (hnp : ¬Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p ∣ Nat.fib n ∧
      ∀ k, 0 < k → k < n → ¬(p ∣ Nat.fib k) := by sorry
