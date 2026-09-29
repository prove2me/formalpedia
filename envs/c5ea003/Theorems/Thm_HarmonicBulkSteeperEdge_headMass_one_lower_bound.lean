-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_headMass_one_lower_bound
-- name    : HarmonicBulkSteeperEdge.headMass_one_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:22.687975+00:00
-- url     : https://prove2.me/theorems/46b86438-bc1a-4b2b-abec-90dc276a6e39
-- title:
--   Non-asymptotic companion.
-- statement:
--   **Non-asymptotic companion.**  For every truncation `n ≥ 1` the harmonic head mass is
--   at least `H(m) / (1 + log n)`; over a bounded range of `n` this is nearly constant.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.headMass_one_lower_bound{m n : ℕ} (hn : 1 ≤ n) :
--       headSum 1 m / (1 + Real.log n) ≤ headMass 1 n m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HarmonicSaturationRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HarmonicSaturationRate.lean#L108

-- Thm stub generated from Probability/HarmonicSaturationRate.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # The saturation rate of the harmonic head dial

  `Probability.HarmonicBulkSteeperEdge` proves the *saturation dichotomy* for the head
  statistic of a discrete power-law kernel `k ↦ k ^ (-a)` on `{1, …, n}`: as the truncation
  `n` grows, the head mass of a fixed window `{1, …, m}` converges to a strictly positive
  limit when `a > 1` and collapses to `0` when `a ≤ 1`.  It says nothing about the *rate*
  of that collapse.

  This file supplies the rate at the harmonic exponent `a = 1`, which is the case relevant
  to the recorded `1/ℓ`-weighted dial:

  * `headMass_one_mul_log_tendsto` — `headMass 1 n m * log n → headSum 1 m = H(m)`.
    The harmonic head dial decays like `H(m) / log n`.
  * `headMass_one_lower_bound` — the non-asymptotic companion:
    `H(m) / (1 + log n) ≤ headMass 1 n m` for every `n ≥ 1`.
  * `headMass_one_ratio_tendsto_one` — consequently, for two fixed windows the *ratio* of
    head masses converges to `H(m₁)/H(m₂)`, so the dial's *shape* stabilises even though
    its level does not.

  Quantitatively this explains the recorded observation that a `1/ℓ`-weighted dial "looks
  saturated by `ℓ = 400`": a `1 / log n` decay changes by only a few percent over any
  experimentally accessible range of `n`, while being asymptotically null.  Saturation to a
  positive limit is a strictly super-harmonic phenomenon.

  The two ingredients are Mathlib's harmonic-number bounds
  `log (n+1) ≤ H_n ≤ 1 + log n` and the identification of `headSum 1 n` with `H_n`.
-/

open Filter Topology

open HarmonicBulkSteeperEdge

/-! ## The harmonic kernel is the reciprocal kernel -/



/-! ## Harmonic-number asymptotics -/





/-! ## The rate of collapse of the harmonic head dial -/

theorem HarmonicBulkSteeperEdge.headMass_one_lower_bound{m n : ℕ} (hn : 1 ≤ n) :
    headSum 1 m / (1 + Real.log n) ≤ headMass 1 n m := by sorry
