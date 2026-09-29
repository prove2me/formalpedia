-- Prove2me | solution 1 for Catalog.Algebra.TokenizerTax.no_additive_budget_table
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:00:02.458984+00:00
-- url     : https://prove2.me/submissions/acee697f-d0b4-42c4-86cc-b47ee1d26178

-- Sol generated from Algebra/TokenizerTaxRigidity.lean
import Mathlib
import Definitions.Def_Algebra_TokenizerTaxMultiplicative
import Definitions.Def_Algebra_TokenizerTaxRigidity
import Theorems.Thm_Catalog_Algebra_TokenizerTax_budget_baseline
import Theorems.Thm_Catalog_Algebra_TokenizerTax_budget_language
/-
# Rigidity of the tokenizer tax: budget tables cannot be separable

`Algebra.TokenizerTaxMultiplicative` established the multiplicative law: in the power-law
recall model the language knob multiplies the key budget by `amp a b lam = lam ^ (b / a)`,
so an additive `+4` fine-step penalty at short context is *amplified* by exactly the
acceleration of the baseline requirement.

The deployment conclusion drawn from NET-88 was that "budget tables must include a
language × context interaction term".  This file proves that as a **rigidity theorem**:

* `language_context_exchange` — the model has an exact scaling symmetry: a fragmenting
  language at context `C` is *the same workload* as the reference language at context
  `lam * C`.  Language and context are one orbit of a single `ℝ>0` action.
* `log_budget_affine` — on a logarithmic scale the budget is affine with the *same*
  slope `b / a` in `log lam` and in `log C`: the interaction is exactly bilinear.
* `no_additive_budget_table` — **rigidity**: if the budget were separable,
  `budget = f C + g lam`, then the amplification factor is forced to be `1`.  Hence
  (`budget_table_needs_interaction`) for any genuinely fragmenting language no additive
  table can exist.  This is not a fitting failure; it is an algebraic impossibility.

The last section adds the *fine-step* layer actually used by the harness: budgets are
spent in a grid of `g` keys, so the reported penalty is `⌈tax / g⌉` steps.

* `steps_quadruple_lower` — a `4×` amplification of the real tax costs at least
  `4 · (fine steps) - 3` steps: rounding cannot hide the explosion.
* `net88_fine_step_jump` — the NET-88 arithmetic: on the grid `g = 4`, a `+4`-key tax is
  one fine step and its amplified `+16`-key form is four.
* `step_tax_unbounded` — no finite fine-step penalty is valid for all contexts.
-/

open Catalog.Algebra.TokenizerTax

open Real

/-! ## The scaling symmetry: language ≡ context -/



/-! ## Rigidity: no separable budget table -/



/-! ## The fine-step grid -/







open Catalog.Algebra.TokenizerTax in
theorem solution{A₀ b a τ lam : ℝ} (hA : 0 < A₀) (ha : 0 < a) (hb : 0 < b)
    (hτ : τ < 1) (hlam : 0 < lam) (f g : ℝ → ℝ)
    (hsep : ∀ l C : ℝ, 0 < l → 0 < C → budget (amplitude A₀ b l C) a τ = f C + g l) :
    amp a b lam = 1 := by
  have h1τ : (0:ℝ) < 1 - τ := by linarith
  set K : ℝ := (A₀ / (1 - τ)) ^ a⁻¹ with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos (div_pos hA h1τ) _
  -- a second context at which the baseline is exactly doubled
  set C₂ : ℝ := (2:ℝ) ^ (a / b) with hC₂def
  have hC₂ : 0 < C₂ := Real.rpow_pos_of_pos (by norm_num) _
  have hC₂pow : C₂ ^ (b / a) = 2 := by
    rw [hC₂def, ← Real.rpow_mul (by norm_num)]
    have : a / b * (b / a) = 1 := by field_simp
    rw [this, Real.rpow_one]
  -- baselines at the two contexts
  have base1 : budget (amplitude A₀ b 1 1) a τ = K := by
    rw [budget_baseline (b := b) hA.le hτ (by norm_num), Real.one_rpow, mul_one]
  have base2 : budget (amplitude A₀ b 1 C₂) a τ = 2 * K := by
    rw [budget_baseline (b := b) hA.le hτ hC₂.le, hC₂pow]
    ring
  -- the four table entries
  have e11 := hsep 1 1 one_pos one_pos
  have e12 := hsep 1 C₂ one_pos hC₂
  have el1 := hsep lam 1 hlam one_pos
  have el2 := hsep lam C₂ hlam hC₂
  rw [budget_language hA.le hτ hlam.le (by norm_num), base1] at el1
  rw [budget_language hA.le hτ hlam.le hC₂.le, base2] at el2
  rw [base1] at e11
  rw [base2] at e12
  -- subtracting the reference row: `(amp - 1) * baseline` must be the same constant
  have d1 : (amp a b lam - 1) * K = g lam - g 1 := by
    have : amp a b lam * K - K = g lam - g 1 := by rw [el1, e11]; ring
    linarith [this]
  have d2 : (amp a b lam - 1) * (2 * K) = g lam - g 1 := by
    have : amp a b lam * (2 * K) - 2 * K = g lam - g 1 := by rw [el2, e12]; ring
    linarith [this]
  have : (amp a b lam - 1) * K = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hKpos.ne'
