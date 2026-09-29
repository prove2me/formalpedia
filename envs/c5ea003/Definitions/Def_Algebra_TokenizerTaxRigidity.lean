-- Prove2me | Definitions.Def_Algebra_TokenizerTaxRigidity
-- name    : Algebra_TokenizerTaxRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:49.284188+00:00
-- url     : https://prove2.me/theorems/0d0d7e2c-3da9-4e71-9e84-c1d62ae58603
-- title:
--   Aether Catalog definitions — Algebra_TokenizerTaxRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TokenizerTaxRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TokenizerTaxRigidity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TokenizerTaxMultiplicative
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

namespace Catalog.Algebra.TokenizerTax

open Real

/-! ## The scaling symmetry: language ≡ context -/



/-! ## Rigidity: no separable budget table -/



/-! ## The fine-step grid -/

/-- The harness spends keys on a grid of width `g`; a real budget `x` costs `⌈x / g⌉`
**fine steps**. -/
noncomputable def steps (g x : ℝ) : ℤ := ⌈x / g⌉





end Catalog.Algebra.TokenizerTax


