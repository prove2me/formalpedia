-- Prove2me | Theorems.Thm_EOSGenericity_prob_indep_and_cure_ge
-- name    : EOSGenericity.prob_indep_and_cure_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:28:13.430985+00:00
-- url     : https://prove2.me/theorems/9ac1591d-b4e3-4fb1-9604-eae2fed2f4b6
-- title:
--   Reliability ∧ genericity.
-- statement:
--   **Reliability ∧ genericity.**  With `k ≤ n` exclusive dimensions, the probability that the
--   boundary token occupies a genuinely `k`-dimensional subspace *and* avoids every obstruction is
--   at least `1 - m·p^{-k} - (p^k-1)/((p-1)p^n)`.  The two error terms move in opposite directions
--   in `k`, so the design optimum is interior.
--
--   ```lean
--   theorem EOSGenericity.prob_indep_and_cure_ge(W : Fin m → Submodule (ZMod p) V) (hW : ∀ j, W j ≠ ⊤) {k : ℕ}
--       (hk : k ≤ finrank (ZMod p) V) :
--       1 - (m : ℝ) / (p : ℝ) ^ k
--           - ((p : ℝ) ^ k - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ (finrank (ZMod p) V))
--         ≤ (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
--             / (Nat.card V : ℝ) ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/EOSExclusiveDimGenericity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/EOSExclusiveDimGenericity.lean#L153

-- Thm stub generated from NumberTheory/EOSExclusiveDimGenericity.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
/-
# Are the exclusive dimensions really exclusive?  A `q`-Pochhammer genericity bound

Companion to `Catalog/NumberTheory/EOSWidthMonotoneRamp.lean`.

The ramp model draws the boundary token's `k` exclusive directions uniformly at random from a
finite `𝔽_p`-space `V` of dimension `n`.  For the phrase "`k` exclusive dimensions" to be
honest, the `k` draws must actually be linearly independent.  This file quantifies that:

* `EOSGenericity.probIndep_eq_prod` — the probability that `k ≤ n` uniform draws are linearly
  independent is exactly the `q`-Pochhammer product `∏_{i<k} (1 - p^{i-n})`
  (via Mathlib's `card_linearIndependent`);
* `EOSGenericity.one_sub_sum_le_prod_one_sub` — a Weierstrass product inequality, proved by
  induction;
* `EOSGenericity.probIndep_ge` — hence `P(independent) ≥ 1 - (p^k - 1)/((p-1) p^n)`: for
  `k ≪ n` the drawn directions are exclusive with overwhelming probability, so the model of
  the companion file is not vacuous;
* `EOSGenericity.probIndep_antitone_step` — genericity decays with `k`, in the opposite
  direction to the reliability ramp;
* `EOSGenericity.prob_indep_and_cure_ge` — **the synthesis**: with `k` exclusive dimensions the
  probability that the token both occupies a genuine `k`-dimensional subspace *and* escapes all
  `m` obstructions is at least

  `1 - m·p^{-k} - (p^k - 1)/((p-1)·p^n)`,

  a two-sided window: the first term (reliability) shrinks geometrically in `k`, the second
  (genericity) grows geometrically in `k`, so the optimal exclusive width is interior — there is
  a genuine trade-off and no cliff.

### Lab notes

With `p = 2`, `n = 192` (the hidden width of the recurrent cell in the motivating experiment)
and `m = 1`, the bound reads `1 - 2^{-k} - (2^k-1)·2^{-192}`: the genericity loss is utterly
negligible up to `k ≈ 100`, so in the regime of the data (`k ≤ 8`) the reliability term alone
governs, matching the observed monotone ramp `0.25 → 0.33 → 0.83 → 1.00 → 1.00`.
-/


open Module Finset

open EOSGenericity

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]






/-! ## Synthesis: reliability and genericity together -/

open EOSWidthRamp in

theorem EOSGenericity.prob_indep_and_cure_ge(W : Fin m → Submodule (ZMod p) V) (hW : ∀ j, W j ≠ ⊤) {k : ℕ}
    (hk : k ≤ finrank (ZMod p) V) :
    1 - (m : ℝ) / (p : ℝ) ^ k
        - ((p : ℝ) ^ k - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ (finrank (ZMod p) V))
      ≤ (Nat.card {v : Fin k → V // LinearIndependent (ZMod p) v ∧ ¬ ∃ j, ∀ i, v i ∈ W j} : ℝ)
          / (Nat.card V : ℝ) ^ k := by sorry
