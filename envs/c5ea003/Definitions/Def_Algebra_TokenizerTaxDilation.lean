-- Prove2me | Definitions.Def_Algebra_TokenizerTaxDilation
-- name    : Algebra_TokenizerTaxDilation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:52.130701+00:00
-- url     : https://prove2.me/theorems/7c4a32cb-29c0-453c-bf51-29bec92cd74e
-- title:
--   Aether Catalog definitions — Algebra_TokenizerTaxDilation
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TokenizerTaxDilation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TokenizerTaxDilation.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Algebra.TokenizerTax

open Real intervalIntegral

/-! ## Dilation budgets -/

/-- A **dilation budget**: a positive key-budget function of the context length which
responds to dilations of the context by a multiplicative factor `chi`. -/
structure DilationBudget where
  /-- key budget needed at context length `C` -/
  B : ℝ → ℝ
  /-- response factor to a dilation of the context -/
  chi : ℝ → ℝ
  B_pos : ∀ C, 0 < C → 0 < B C
  dilate : ∀ u C, 0 < u → 0 < C → B (u * C) = chi u * B C

namespace DilationBudget

variable (D : DilationBudget)

/-- The tax charged by a language whose fragmentation ratio is `lam`. -/
noncomputable def langTax (lam C : ℝ) : ℝ := D.B (lam * C) - D.B C







end DilationBudget

/-! ## Model 1: the power-law recall model -/

/-- The power-law model of `Algebra.TokenizerTaxMultiplicative`, packaged as a dilation
budget.  Its character is `u ↦ u ^ (b / a)`. -/
noncomputable def powerLawDilation (A₀ b a τ : ℝ) (hA : 0 < A₀) (hτ : τ < 1) :
    DilationBudget where
  B C := (A₀ / (1 - τ)) ^ a⁻¹ * C ^ (b / a)
  chi u := u ^ (b / a)
  B_pos C hC := by
    have h1τ : (0:ℝ) < 1 - τ := by linarith
    exact mul_pos (Real.rpow_pos_of_pos (div_pos hA h1τ) _) (Real.rpow_pos_of_pos hC _)
  dilate u C hu hC := by
    rw [Real.mul_rpow hu.le hC.le]
    ring



/-! ## Model 2: a continuum Zipf attention profile -/



/-- The Zipf key budget: the exact number of keys needed to clear the bar `τ`. -/
noncomputable def zipfBudget (s τ C : ℝ) : ℝ := τ ^ (1 - s)⁻¹ * C


/-- The Zipf model as a dilation budget: its character is the identity, `chi u = u`. -/
noncomputable def zipfDilation (s τ : ℝ) (hτ : 0 < τ) : DilationBudget where
  B C := zipfBudget s τ C
  chi u := u
  B_pos C hC := mul_pos (Real.rpow_pos_of_pos hτ _) hC
  dilate u C _ _ := by unfold zipfBudget; ring





/-! ## Falsifiable predictions for the next experimental cells -/

namespace DilationBudget

variable (D : DilationBudget)



end DilationBudget


end Catalog.Algebra.TokenizerTax


