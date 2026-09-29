-- Prove2me | Theorems.Thm_EOSGenericity_one_sub_sum_le_prod_one_sub
-- name    : EOSGenericity.one_sub_sum_le_prod_one_sub
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:27:24.029725+00:00
-- url     : https://prove2.me/theorems/f66f1f91-50f7-431f-aa68-d1e5e90e4f01
-- title:
--   Weierstrass product inequality (proved by induction): for `0 ≤ aᵢ ≤ 1`,
-- statement:
--   **Weierstrass product inequality** (proved by induction): for `0 ≤ aᵢ ≤ 1`,
--   `1 - ∑ aᵢ ≤ ∏ (1 - aᵢ)`.
--
--   ```lean
--   theorem EOSGenericity.one_sub_sum_le_prod_one_sub(a : ℕ → ℝ) (k : ℕ)
--       (h0 : ∀ i ∈ range k, 0 ≤ a i) (h1 : ∀ i ∈ range k, a i ≤ 1) :
--       1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/EOSExclusiveDimGenericity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/EOSExclusiveDimGenericity.lean#L88

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

theorem EOSGenericity.one_sub_sum_le_prod_one_sub(a : ℕ → ℝ) (k : ℕ)
    (h0 : ∀ i ∈ range k, 0 ≤ a i) (h1 : ∀ i ∈ range k, a i ≤ 1) :
    1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by sorry
