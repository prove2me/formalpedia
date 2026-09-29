-- Prove2me | Definitions.Def_MachineLearning_PosetTheory_RademacherComplexity
-- name    : MachineLearning_PosetTheory_RademacherComplexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:15.263926+00:00
-- url     : https://prove2.me/theorems/2dedf0bd-609e-4b1a-be97-3812b3a97938
-- title:
--   Aether Catalog definitions — MachineLearning_PosetTheory_RademacherComplexity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PosetTheory.RademacherComplexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PosetTheory/RademacherComplexity.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. Released under Apache 2.0 license.

# Empirical Rademacher Complexity of Finite Function Classes

This file gives a fully rigorous, self-contained development of the *empirical
Rademacher complexity* of a finite class of real-valued functions evaluated on a
fixed sample of size `m`.  Rademacher complexity is the central data-dependent
capacity measure of statistical learning theory; it controls uniform deviation
bounds and hence generalization error.

We represent a hypothesis evaluated on a sample of size `m` by its vector of
values `f : Fin m → ℝ`.  A Rademacher sign assignment is `σ : Fin m → Bool`,
interpreted via `radSign` as `±1`.  The empirical Rademacher complexity averages
the best-correlating member of the class over *all* `2^m` sign assignments.

This complements the algebraic capacity theory in `Foundations.lean`
(VC dimension, `spectralComplexityBound`, `algebraicSampleComplexityBound`,
whose `8/3` constant arises from the Rademacher-to-PAC conversion) by giving the
*analytic* object those bounds approximate, with exact computations rather than
inequalities.

## Main results

* `sum_radSign`            — the signed indicator of any coordinate cancels over all sign vectors
* `radSum_sum_zero`        — the Rademacher correlation of a fixed function averages to zero
* `radSum_neg`             — Rademacher correlation is odd in the function
* `empRad_singleton`       — the empirical Rademacher complexity of a singleton class is `0`
* `empRad_mono`            — monotonicity of complexity under class inclusion
* `empRad_nonneg`          — complexity is nonnegative for any class containing the zero function
* `empRad_symmetric_pair`  — *exact* formula for the symmetric pair `{f, -f}` (the building block)
-/


open BigOperators

/-! ## Rademacher signs and correlations -/

/-- The `±1` Rademacher sign attached to a Boolean sign vector at coordinate `i`. -/
def radSign {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : ℝ := if σ i then 1 else -1

/-- The Rademacher correlation of a sample-value vector `f` with sign vector `σ`,
i.e. `∑ i, σ_i f_i`. -/
def radSum {m : ℕ} (f : Fin m → ℝ) (σ : Fin m → Bool) : ℝ := ∑ i, radSign σ i * f i

/-- The **empirical Rademacher complexity** of a nonempty finite function class `F`
on a sample of size `m`: the sample-normalized average over all `2^m` sign vectors
of the best-correlating member of the class. -/
noncomputable def empRad {m : ℕ} (F : Finset (Fin m → ℝ)) (hF : F.Nonempty) : ℝ :=
  (1 / (m : ℝ)) * (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool, F.sup' hF (fun f => radSum f σ)

/-! ## Core cancellation identity -/

-- !-- The signed indicator of a fixed coordinate sums to zero over all sign
-- vectors: pair each `σ` with the one obtained by flipping coordinate `i`; the
-- two values `+1` and `-1` cancel, giving a fixed-point-free involution. -- !--

-- !-- Expand `radSum`, swap the order of summation, and factor each coordinate's
-- contribution through `sum_radSign`. -- !--

-- !-- Distribute negation through the sum defining `radSum`. -- !--

/-! ## Structural properties of empirical Rademacher complexity -/

-- !-- The supremum over a singleton collapses to the single value, and
-- `radSum_sum_zero` makes the resulting average vanish. -- !--

-- !-- The supremum over a subclass is dominated by the supremum over the larger
-- class for every sign vector; summing and multiplying by the nonnegative
-- normalization constant preserves the inequality. -- !--

-- !-- For every sign vector the supremum dominates the value at the zero
-- function, which is `0`; hence each summand is nonnegative. -- !--

/-! ## The symmetric pair: an exact formula -/

-- !-- For each sign vector the supremum over `{f, -f}` is `max (radSum f σ)
-- (-radSum f σ) = |radSum f σ|` by `radSum_neg` and `abs_eq_max_neg`. -- !--

-- !-- Immediate from the exact formula since each `|radSum f σ|` is nonnegative
-- and the normalization constant is nonnegative. -- !--


