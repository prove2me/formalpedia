-- Prove2me | Theorems.Thm_PositionalStratum_value_universality_fails
-- name    : PositionalStratum.value_universality_fails
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:47.195413+00:00
-- url     : https://prove2.me/theorems/38cf4564-3cb7-432a-b0ce-3b3a02586579
-- title:
--   Value-universality is false off uniform cells, and the failure is unbounded.
-- statement:
--   **Value-universality is false off uniform cells, and the failure is unbounded.**
--   For every bound `B` there is a positional-stratum instance — a head stratum of size `m`
--   inside `M = 2m` slots, honouring the booked capture probability `P` *exactly* — whose true
--   expected scan cost is smaller than the booked (uniform-cell) prediction by a factor
--   exceeding `B`.  Hence the booked *value* (speedup) law is not an upper bound off uniform
--   cells, even though the master inequality above stays valid.
--
--   ```lean
--   theorem PositionalStratum.value_universality_fails(B : ℝ) :
--       ∃ (M m : ℕ) (P : ℝ) (w : ℕ → ℝ), 0 < m ∧ m < M ∧ 0 < P ∧ P < 1 ∧
--         (∀ i, 0 ≤ w i) ∧
--         mass (positions m) w = P ∧
--         mass (positions M) w = 1 ∧
--         0 < EC M scanCost w ∧
--         B * EC M scanCost w < bookedEC M m P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumMeasure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumMeasure.lean#L408

-- Thm stub generated from Applications/PositionalStratumMeasure.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
/-
# Positional-stratum measure framework (GAP-L4)

A self-contained finite-measure framework for *positional strata* in one-shot
search / retrieval cost models.

The setting is elementary but the statements are the ones that carry the load:

* `positions M` — the ranked slots `1, …, M`;
* a *weight* `w : ℕ → ℝ`, the probability of the target sitting at a given slot;
* a *cost kernel* `c : ℕ → ℝ`, the number of probes charged when the target is resolved
  at that slot.  Two kernels matter: the **scan kernel** `c i = i` (sequential probing)
  and the **block-commitment kernel** (constant on each stratum), which is the one behind
  the certified law of `PositionalStratumCertifiedLaw`.

Main results.

* `rbar_identity` : the universal object,  `EC = P · r̄_R + (1 - P) · r̄_C`, an *exact*
  identity for every weight, every cost kernel and every stratum of nondegenerate mass.
* `theta_eq_one_of_uniform` / `uniform_of_forall_theta_eq_one` : the booking factor
  `Θ = r̄_R / (cell centre)` equals `1` on uniform cells, and if it equals `1` on
  *every* cell then the weight is uniform.  The single-cell converse is **false**:
  `theta_eq_one_not_uniform` is an explicit non-uniform witness with `Θ = 1`.
* `scan_cost_le_baseline` : the majorization / Chebyshev step — a descending (antitone)
  weight has expected scan cost at most the full-scan baseline `C₀ = (M+1)/2`.
* `exchange_inequality`, `sorted_le_of_antitone` : the rearrangement step.
* `exists_large_bucket`, `speedup_le_two_pow_kbits` : the `k_bits` (pigeonhole) branch.
* `master_inequality`, `master_inequality_of_filter` :
  `S ≤ min (1/(Λ·Θ·q̂)) (2^k/(Λ·Θ))`.
* `value_universality_fails` : the booked (uniform-cell) value law is **not** universal —
  off uniform cells the true speedup exceeds the booked one by an *unbounded* factor.
-/

open PositionalStratum

open Finset

noncomputable section

/-! ## The finite positional space -/












/-! ## The r̄-identity : the universal object -/



/-! ## The booking factor `Θ` : uniformity detection -/




/-! ## Majorization : the descending weight beats the baseline -/





/-! ## The `k_bits` branch : pigeonhole on the filter -/



/-! ## The master inequality -/



/-! ## Off uniform cells the *value* law is not universal -/

theorem PositionalStratum.value_universality_fails(B : ℝ) :
    ∃ (M m : ℕ) (P : ℝ) (w : ℕ → ℝ), 0 < m ∧ m < M ∧ 0 < P ∧ P < 1 ∧
      (∀ i, 0 ≤ w i) ∧
      mass (positions m) w = P ∧
      mass (positions M) w = 1 ∧
      0 < EC M scanCost w ∧
      B * EC M scanCost w < bookedEC M m P := by sorry
