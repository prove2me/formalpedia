-- Prove2me | Theorems.Thm_KneeStaircase_abundancy_strict_mono_shift
-- name    : KneeStaircase.abundancy_strict_mono_shift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:29:18.550523+00:00
-- url     : https://prove2.me/theorems/4e95d44b-84f9-4395-ba27-c6a4d8ec3596
-- title:
--   Strict monotonicity of abundancy under doubling.
-- statement:
--   **Strict monotonicity of abundancy under doubling.**  Written multiplicatively to stay in `ℕ`:
--   `σ(k)/k < σ(2k)/(2k)` for `k = stair b j`.  Doubling the zero block always makes the rung more
--   abundant — the seed jitter `96 → 112 → 128` moves *down* the ladder in this order.
--
--   ```lean
--   theorem KneeStaircase.abundancy_strict_mono_shift{b j : ℕ} (hj : 1 ≤ j) :
--       (∑ d ∈ (stair b j).divisors, d) * stair (b + 1) j
--         < (∑ d ∈ (stair (b + 1) j).divisors, d) * stair b j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/KneeStaircaseDivisorSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/KneeStaircaseDivisorSpectrum.lean#L216

-- Thm stub generated from NumberTheory/KneeStaircaseDivisorSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_KneeStaircaseArithmetic
/-
# The divisor spectrum of the staircase family: abundance, perfection, and the NET-47 boundary

Companion to `Catalog/NumberTheory/KneeStaircaseArithmetic.lean`, where the NET-47 knee triple
`{96, 112, 128}` at `(d = 4, ctx = 1024)` was identified with the top of the binary staircase
ladder `stair b j = 2 ^ b (2 ^ j - 1)` together with its top point `2 ^ 7`.

Here we compute the divisor sum of the whole family and classify its members.  The outcome is a
sharp arithmetic dichotomy running straight through the measured data:

* `KneeStaircase.sum_divisors_stair` — `σ(stair b j) = (2^(b+1) - 1) · σ(2^j - 1)`, from the
  2-adic splitting of the staircase normal form.
* `KneeStaircase.stair_abundant` — every staircase number with `2 ≤ j ≤ b` is **abundant**.  Both
  *jittered* knees `96 = stair 5 2` and `112 = stair 4 3` qualify.
* `KneeStaircase.stair_deficient_of_one` — the `j = 1` rungs are the powers of two, which are
  **deficient**.  The *product point* `128 = 2 ^ 7` is one of them
  (`KneeStaircase.net47_product_point_deficient`).
* `KneeStaircase.stair_perfect_of_mersenne_prime` (Euclid direction) and
  `KneeStaircase.stair_perfect_iff` (Euler direction, proved here from scratch for the family):
  for `1 ≤ b`, `stair b j` is **perfect** iff `j = b + 1` and `2 ^ j - 1` is prime.  In
  particular no rung of the weight-7 ladder is perfect (`KneeStaircase.net47_no_knee_perfect`):
  the only candidate `120 = stair 3 4` fails precisely because `15` is composite.
* `KneeStaircase.abundancy_strict_mono_shift` — the abundancy index increases strictly along the
  shift `b ↦ b + 1`, and
* `KneeStaircase.abundancy_tendsto` — a bridge to analysis: along the shift direction the
  abundancy index converges to `2 σ(2^j - 1) / (2^j - 1)`.  The staircase family therefore has a
  *finite* abundancy ceiling for each fixed number of ones; abundance in this family is a
  statement about the ratio of `b` to `j`, not about size.
* `KneeStaircase.net47_jitter_crosses_perfect_boundary` — the reading of the round: the two
  jittered knees are abundant, the product point is deficient.  The ±16 seed jitter observed at
  `(d = 4, ctx = 1024)` moves the knee across the perfect-number boundary.
-/


open KneeStaircase

open Finset

/-! ## 1.  The divisor sum of a staircase number -/








/-! ## 2.  Abundance -/



/-! ## 3.  Perfection: Euclid and Euler for the staircase family -/




/-! ## 4.  The abundancy index along the shift direction -/

theorem KneeStaircase.abundancy_strict_mono_shift{b j : ℕ} (hj : 1 ≤ j) :
    (∑ d ∈ (stair b j).divisors, d) * stair (b + 1) j
      < (∑ d ∈ (stair (b + 1) j).divisors, d) * stair b j := by sorry
