-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_headSum_sandwich_upper
-- name    : HarmonicBulkSteeperEdge.headSum_sandwich_upper
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:43:50.931581+00:00
-- url     : https://prove2.me/theorems/f84e9aec-82e7-4dd9-a3f0-95a5acd44289
-- title:
--   Upper half of the sandwich.
-- statement:
--   **Upper half of the sandwich.**  Comparing the sum, minus its first term, with the
--   integral of the antitone kernel over `[1, n]`.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.headSum_sandwich_upper{a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
--       headSum a n ≤ 1 + ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SubHarmonicSaturationRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SubHarmonicSaturationRate.lean#L64

-- Thm stub generated from Probability/SubHarmonicSaturationRate.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # The saturation rate below the harmonic exponent

  `Probability.HarmonicBulkSteeperEdge` proves the *saturation dichotomy* for the head
  statistic of a discrete power-law kernel `k ↦ k ^ (-a)` on `{1, …, n}`: the head mass of
  a fixed window `{1, …, m}` tends to a positive limit iff `a > 1`, and collapses to `0`
  for `a ≤ 1`.  `Probability.HarmonicSaturationRate` pins the *rate* of that collapse at
  the harmonic exponent `a = 1`, where it is logarithmic: `headMass 1 n m · log n → H(m)`.

  This file closes the remaining half of the rate question — the *sub-harmonic* regime
  `0 ≤ a < 1`, where the collapse is polynomial rather than logarithmic:

  * `headSum_sandwich_lower` / `headSum_sandwich_upper` — the non-asymptotic two-sided
    bound `((n+1)^{1-a} - 1)/(1-a) ≤ headSum a n ≤ 1 + (n^{1-a} - 1)/(1-a)`, obtained by
    monotone sum/integral comparison for the antitone kernel `x ↦ x^{-a}`.
  * `headSum_div_rpow_tendsto` — consequently `headSum a n / n^{1-a} → 1/(1-a)`.
  * `headMass_mul_rpow_tendsto` — the rate itself:
    `headMass a n m · n^{1-a} → (1-a) · headSum a m`.
  * `headMass_doubling_ratio_tendsto` — the calibration corollary: *doubling* the
    truncation multiplies the dial asymptotically by `2^{a-1}`.  (Contrast the harmonic
    case, where doubling is asymptotically neutral and *squaring* halves the dial.)

  Together with `HarmonicSaturationRate` this fixes the truncation artefact for every
  exponent `a ≤ 1`, so recorded dials taken at different truncations become comparable:
  at `a < 1` the level scales like `n^{a-1}`, at `a = 1` like `1 / log n`, and only for
  `a > 1` does it saturate.
-/

open Filter Topology

open HarmonicBulkSteeperEdge

/-! ## The kernel is antitone on the positive reals -/


/-! ## Non-asymptotic sandwich for the truncated sum -/

theorem HarmonicBulkSteeperEdge.headSum_sandwich_upper{a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
    headSum a n ≤ 1 + ((n : ℝ) ^ (1 - a) - 1) / (1 - a) := by sorry
