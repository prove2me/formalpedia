-- Prove2me | Theorems.Thm_Bishop_Reg_toReal_mul
-- name    : Bishop.Reg.toReal_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:17:38.569987+00:00
-- url     : https://prove2.me/theorems/ba7dd944-3da4-456f-91e1-5f635509859b
-- title:
--   ToReal mul
-- statement:
--   Formal statement of `Bishop.Reg.toReal_mul` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bishop.Reg.toReal_mul(x y : Reg) : (mul x y).toReal = x.toReal * y.toReal := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ComputableReals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ComputableReals.lean#L219

-- Thm stub generated from Logic/ConstructiveAnalysis/ComputableReals.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
/-
# Computable arithmetic on Bishop reals, and a concrete computable irrational

The Bishop reals of `Logic/ConstructiveAnalysis/BishopReals.lean` are *data*: a
regular sequence of rationals is a computable object whenever its approximating
function is.  This file supplies the basic algebraic operations in Bishop's
explicit form — with the index shifts that make the results regular again — and
verifies that they compute the classical operations under `toReal`.

* `Bishop.Reg.ofRat`, `Reg.neg`, `Reg.add`, `Reg.mul` are ordinary (computable)
  definitions; only `toReal` is noncomputable.
* `Bishop.Reg.toReal_ofRat`, `toReal_neg`, `toReal_add`, `toReal_mul` verify them.
* `Bishop.sqrtTwo` is an explicitly computable Bishop real (its `n`-th approximation
  is `⌊√(2(n+1)²)⌋/(n+1)`, computed with `Nat.sqrt`), and
  `Bishop.toReal_sqrtTwo`, `Bishop.sqrtTwo_sq` prove that it denotes `√2`.
-/


open Bishop

open Reg

/-! ## Rational constants -/




/-! ## Negation -/




/-! ## Addition -/




/-! ## Multiplication

Multiplication needs an explicit *bound* for the factors; Bishop's canonical bound
`⌈|x₀|⌉ + 2` is used, and the index shift is by the sum of the two bounds. -/

theorem Bishop.Reg.toReal_mul(x y : Reg) : (mul x y).toReal = x.toReal * y.toReal := by sorry
