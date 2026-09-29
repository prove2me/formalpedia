-- Prove2me | solution 1 for Catalog.Algebra.TokenizerTax.amp_eq_identity_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:58:21.027588+00:00
-- url     : https://prove2.me/submissions/d48e1547-acc1-4d1a-bc3d-4874a7e2a49d

-- Sol generated from Algebra/TokenizerTaxDilation.lean
import Mathlib
import Definitions.Def_Algebra_TokenizerTaxDilation
import Definitions.Def_Algebra_TokenizerTaxMultiplicative
/-
# The multiplicative law is model-independent: dilation budgets and their characters

`Algebra.TokenizerTaxMultiplicative` proved the NET-88 multiplicative law inside one
concrete family (the power-law recall model).  A critic is entitled to ask whether the
law is an artefact of that family.  This file answers: **no** — the law follows from a
single structural property, and a completely different micro-model (a continuum Zipf
attention profile, whose retention curve is *computed here from an integral*, not
postulated) satisfies the same property.

## The structure

A `DilationBudget` is a positive budget function `B` of the context length together with
a factor `chi` describing how `B` responds to a dilation of the context:
`B (u * C) = chi u * B C`.  A language shift acts precisely as such a dilation — German
prose at context `C` is the reference workload at context `lam * C` — so every language
tax is `(chi lam - 1) * B C`.

* `DilationBudget.chi_mul`, `chi_one` — `chi` is *forced* to be a character of the
  dilation monoid; multiplicativity is derived, not assumed.
* `DilationBudget.tax_amplification` — the multiplicative law in its structural form:
  `tax C₂ * B C₁ = tax C₁ * B C₂`.  Amplification of the tax = acceleration of the
  baseline, in any model of the structure.
* `DilationBudget.tax_constant_iff_trivial` — the tax is context-independent iff the
  language is free or the baseline is dilation-invariant: P3 has no room.

## Two models

* `powerLawDilation` — the model of `Algebra.TokenizerTaxMultiplicative`, with character
  `chi u = u ^ (b / a)`.
* `zipfDilation` — a continuum Zipf attention profile `x ↦ x ^ (-s)` on `(0, C]` with
  `s < 1`.  Here `zipf_retained_eq_ratio` *derives* the retention curve
  `retained = (k / C) ^ (1 - s)` from the exact mass integrals, `zipf_gate_iff` shows the
  gate is exactly `k ≥ τ ^ (1 - s)⁻¹ * C`, and the resulting budget is a dilation budget
  with character `chi u = u`.

Both models therefore obey `tax_amplification`; the `4×` amplification observed at
ctx = 4096 is a structural, not a parametric, phenomenon.
-/

open Catalog.Algebra.TokenizerTax

open Real intervalIntegral

/-! ## Dilation budgets -/


open DilationBudget

variable (D : DilationBudget)









/-! ## Model 1: the power-law recall model -/




/-! ## Model 2: a continuum Zipf attention profile -/










/-! ## Falsifiable predictions for the next experimental cells -/

open DilationBudget

variable (D : DilationBudget)






open Catalog.Algebra.TokenizerTax in
theorem solution{a b lam : ℝ} (ha : 0 < a) (hlam : 1 < lam) :
    amp a b lam = lam ↔ b = a := by
  unfold amp
  constructor
  · intro h
    have h' : lam ^ (b / a) = lam ^ (1:ℝ) := by rw [Real.rpow_one]; exact h
    have h1 : b / a ≤ 1 := (Real.rpow_le_rpow_left_iff hlam).1 h'.le
    have h2 : (1:ℝ) ≤ b / a := (Real.rpow_le_rpow_left_iff hlam).1 h'.ge
    have hba : b / a = 1 := le_antisymm h1 h2
    field_simp at hba
    linarith
  · intro h
    subst h
    rw [div_self ha.ne', Real.rpow_one]
