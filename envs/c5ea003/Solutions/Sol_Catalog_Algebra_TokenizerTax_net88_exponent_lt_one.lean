-- Prove2me | solution 1 for Catalog.Algebra.TokenizerTax.net88_exponent_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:58:23.169787+00:00
-- url     : https://prove2.me/submissions/d499334f-ad6f-4732-864b-a78c005b2f3a

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
theorem solution{A a : ℝ}
    (h24 : deficit A a 24 = 0.047) (h56 : deficit A a 56 = 0.024) : a < 1 := by
  by_contra hcon
  push_neg at hcon
  have h24p : (0:ℝ) < (24:ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have h56p : (0:ℝ) < (56:ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have e24 : A = 0.047 * (24:ℝ) ^ a := by
    unfold deficit at h24
    rw [Real.rpow_neg (by norm_num)] at h24
    field_simp at h24
    linarith [h24]
  have e56 : A = 0.024 * (56:ℝ) ^ a := by
    unfold deficit at h56
    rw [Real.rpow_neg (by norm_num)] at h56
    field_simp at h56
    linarith [h56]
  -- hence `(56/24) ^ a = 47/24`, but `a ≥ 1` forces `(56/24) ^ a ≥ 56/24 > 47/24`
  have key : (0.024:ℝ) * (56:ℝ) ^ a = 0.047 * (24:ℝ) ^ a := by rw [← e56, ← e24]
  have hratio : ((56:ℝ) / 24) ^ a = 0.047 / 0.024 := by
    rw [Real.div_rpow (by norm_num) (by norm_num)]
    field_simp
    linarith [key]
  have hbig : (56:ℝ) / 24 ≤ ((56:ℝ) / 24) ^ a := by
    calc (56:ℝ) / 24 = ((56:ℝ) / 24) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ ((56:ℝ) / 24) ^ a := Real.rpow_le_rpow_left_iff (by norm_num) |>.2 hcon
  rw [hratio] at hbig
  norm_num at hbig
