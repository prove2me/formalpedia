-- Prove2me | Theorems.Thm_Catalog_Algebra_TokenizerTax_no_additive_budget_table
-- name    : Catalog.Algebra.TokenizerTax.no_additive_budget_table
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:30.006254+00:00
-- url     : https://prove2.me/theorems/5e8c2011-5a6c-4f1a-8a6c-49b96634a98e
-- title:
--   Rigidity of the budget table.
-- statement:
--   **Rigidity of the budget table.**  Suppose someone proposes a budget table that is
--   *separable*: a context column `f C` plus a language surcharge `g lam`, with no interaction
--   term.  Then the amplification factor must be trivial.  Equivalently: an additive
--   language surcharge is only consistent with the model if there is no surcharge at all.
--
--   ```lean
--   theorem Catalog.Algebra.TokenizerTax.no_additive_budget_table{A₀ b a τ lam : ℝ} (hA : 0 < A₀) (ha : 0 < a) (hb : 0 < b)
--       (hτ : τ < 1) (hlam : 0 < lam) (f g : ℝ → ℝ)
--       (hsep : ∀ l C : ℝ, 0 < l → 0 < C → budget (amplitude A₀ b l C) a τ = f C + g l) :
--       amp a b lam = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TokenizerTaxRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TokenizerTaxRigidity.lean#L66

-- Thm stub generated from Algebra/TokenizerTaxRigidity.lean
import Mathlib
import Definitions.Def_Algebra_TokenizerTaxMultiplicative
import Definitions.Def_Algebra_TokenizerTaxRigidity
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

theorem Catalog.Algebra.TokenizerTax.no_additive_budget_table{A₀ b a τ lam : ℝ} (hA : 0 < A₀) (ha : 0 < a) (hb : 0 < b)
    (hτ : τ < 1) (hlam : 0 < lam) (f g : ℝ → ℝ)
    (hsep : ∀ l C : ℝ, 0 < l → 0 < C → budget (amplitude A₀ b l C) a τ = f C + g l) :
    amp a b lam = 1 := by sorry
