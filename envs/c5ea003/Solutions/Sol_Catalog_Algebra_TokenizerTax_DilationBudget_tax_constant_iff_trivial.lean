-- Prove2me | solution 1 for Catalog.Algebra.TokenizerTax.DilationBudget.tax_constant_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:06:09.359448+00:00
-- url     : https://prove2.me/submissions/f6aca8e0-88fb-482f-a056-10deb05f7bd5

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




namespace Catalog.Algebra.TokenizerTax.DilationBudget

variable (D : DilationBudget)

/-- The tax is a fixed multiple of the baseline. -/
theorem langTax_eq {lam C : ℝ} (hlam : 0 < lam) (hC : 0 < C) :
    D.langTax lam C = (D.chi lam - 1) * D.B C := by
  unfold langTax
  rw [D.dilate lam C hlam hC]
  ring

end Catalog.Algebra.TokenizerTax.DilationBudget





/-! ## Model 1: the power-law recall model -/




/-! ## Model 2: a continuum Zipf attention profile -/










/-! ## Falsifiable predictions for the next experimental cells -/

open DilationBudget

variable (D : DilationBudget)






open Catalog.Algebra.TokenizerTax in
theorem solution{lam C₁ C₂ : ℝ} (hlam : 0 < lam) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) :
    D.langTax lam C₁ = D.langTax lam C₂ ↔ (D.chi lam = 1 ∨ D.B C₁ = D.B C₂) := by
  rw [D.langTax_eq hlam hC₁, D.langTax_eq hlam hC₂]
  constructor
  · intro h
    have hz : (D.chi lam - 1) * (D.B C₁ - D.B C₂) = 0 := by
      rw [mul_sub]
      exact sub_eq_zero.2 h
    rcases mul_eq_zero.1 hz with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]
