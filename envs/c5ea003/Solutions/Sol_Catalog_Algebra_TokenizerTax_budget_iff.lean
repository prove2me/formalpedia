-- Prove2me | solution 1 for Catalog.Algebra.TokenizerTax.budget_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:58:22.016541+00:00
-- url     : https://prove2.me/submissions/29aa9328-d1cd-4250-9805-12de613e4a87

-- Sol generated from Algebra/TokenizerTaxMultiplicative.lean
import Mathlib
import Definitions.Def_Algebra_TokenizerTaxMultiplicative
/-
# The algebra of the tokenizer tax: why a `+4` key tax becomes `+16` at long context

## The experiment (NET-88, German prose, ctx = 4096, gate exact, 3 held-out windows)

| k        | 24    | 32    | 40    | 48    | 56    |
|----------|-------|-------|-------|-------|-------|
| retained | 0.953 | 0.966 | 0.973 | 0.975 | 0.976 |

Every point fails the `0.98` bar; the additive `+4` fine-step penalty that a language
shift costs at short context has grown to `≥ +16` at `4096`, an exact `4×` amplification
matching the acceleration of the baseline requirement itself.

## The model formalised here

The measured curve is a *power-law recall deficit*

`deficit A a k = A * k ^ (-a)`,   `retained = 1 - deficit`,

a two-parameter family whose log–log fit to the table above is `a ≈ 0.810`, `A ≈ 0.582`
(see `ComputationalEvidence.md`; residuals `< 0.004` on all five points).  The *amplitude*
`A` is where the two experimental knobs enter:

* the **context length** `C`, through `A = A₀ * C ^ b` (longer context ⇒ more mass to
  recover), and
* the **language**, through a *fragmentation ratio* `lam`: German prose spends `lam > 1`
  tokens per unit of English content, so the effective context is `lam * C`.

The exact key budget needed to clear a retention bar `τ` is then
`budget A a τ = (A / (1 - τ)) ^ a⁻¹` (`budget_iff` proves this is *exactly* the
requirement, not a bound).

## What is proved

* `budget_iff` — the budget functional is the exact threshold of the retention gate.
* `budget_smul` — `budget` is homogeneous of degree `a⁻¹` in the amplitude: the language
  and context knobs act on it by *multiplication*.
* `ampHom` — the amplification factor `lam ↦ lam ^ (b / a)` is a monoid homomorphism
  `ℝ≥0 →* ℝ≥0` (the tax is a *character* of the fragmentation group), and
  `amplification_universal` shows it is independent of the bar `τ` and of `A₀`.
* `tax_eq_amp_mul_baseline`, `tax_amplification` — **the multiplicative law**: the
  additive tax is a fixed multiple of the baseline requirement, hence its amplification
  between two contexts *equals* the acceleration of the baseline.  `tax_four_to_sixteen`
  is the NET-88 instance: baseline `×4` forces `+4 ↦ +16`.
* `tax_unbounded`, `tax_not_constant` — P2/P3 refuted: the tax neither dissolves nor
  stays at a fixed additive offset; it diverges.
* `budget_superlinear_of_exponent_lt_one` — the *explosion*: because the measured recall
  exponent satisfies `a < 1`, the budget responds *superlinearly* to the amplitude, so the
  tax factor `lam ^ (b / a)` strictly exceeds the naive token ratio `lam ^ b`.
* `net88_exponent_lt_one` — `a < 1` is *forced* by the two measured anchors
  `deficit 24 = 0.047`, `deficit 56 = 0.024`; it is not an assumption.
* `net88_all_points_fail`, `net88_budget_gt_56` — from the single measured anchor at
  `k = 56` the whole row fails and the true requirement exceeds `56`.
-/

open Catalog.Algebra.TokenizerTax

open Real

/-! ## The power-law recall model -/






/-! ### Elementary positivity and monotonicity -/





/-! ## The budget functional is the exact gate threshold -/


/-! ## Homogeneity: the two knobs act multiplicatively -/




/-! ## The amplification factor is a character of the fragmentation group -/







/-! ## The multiplicative law: amplification of the tax = acceleration of the baseline -/






/-! ## P2 and P3 refuted: the tax neither dissolves nor stays put -/



/-! ## The explosion: a sub-linear recall exponent makes the budget super-linear -/



/-! ## The measured anchors -/






open Catalog.Algebra.TokenizerTax in
theorem solution{A a τ k : ℝ} (hA : 0 < A) (ha : 0 < a) (hτ : τ < 1) (hk : 0 < k) :
    τ ≤ retained A a k ↔ budget A a τ ≤ k := by
  have h1τ : (0:ℝ) < 1 - τ := by linarith
  have hka : (0:ℝ) < k ^ a := Real.rpow_pos_of_pos hk a
  have step1 : τ ≤ retained A a k ↔ A / (1 - τ) ≤ k ^ a := by
    unfold retained deficit
    rw [Real.rpow_neg hk.le, ← div_eq_mul_inv, div_le_iff₀ h1τ]
    constructor
    · intro h
      have h2 : A / k ^ a ≤ 1 - τ := by linarith
      rw [div_le_iff₀ hka] at h2
      linarith
    · intro h
      have h2 : A / k ^ a ≤ 1 - τ := by
        rw [div_le_iff₀ hka]
        linarith
      linarith
  rw [step1]
  unfold budget
  constructor
  · intro h
    have := (Real.rpow_le_rpow_iff (le_of_lt (div_pos hA h1τ)) hka.le (inv_pos.2 ha)).2 h
    rwa [Real.rpow_rpow_inv hk.le ha.ne'] at this
  · intro h
    have := (Real.rpow_le_rpow_iff (Real.rpow_nonneg (le_of_lt (div_pos hA h1τ)) _) hk.le ha).2 h
    rwa [Real.rpow_inv_rpow (le_of_lt (div_pos hA h1τ)) ha.ne'] at this
