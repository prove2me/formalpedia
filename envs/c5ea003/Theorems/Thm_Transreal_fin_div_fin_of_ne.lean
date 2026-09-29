-- Prove2me | Theorems.Thm_Transreal_fin_div_fin_of_ne
-- name    : Transreal.fin_div_fin_of_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:44.28334+00:00
-- url     : https://prove2.me/theorems/d1824379-8990-4cdb-a94e-31da212441cc
-- title:
--   Exact conservativity of guarded division.
-- statement:
--   **Exact conservativity of guarded division.**  Away from a zero denominator
--   the transreal quotient of two finite values is the finite real quotient.
--
--   ```lean
--   theorem Transreal.fin_div_fin_of_ne{x y : ℝ} (hy : y ≠ 0) :
--       fin x / fin y = fin (x / y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/Transreal/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/Transreal/Core.lean#L195

-- Thm stub generated from Cryptography/Transreal/Core.lean
import Mathlib
import Definitions.Def_Cryptography_Transreal_Core

/-!
# The four-constructor transreal carrier and its arithmetic

This file introduces the carrier used throughout the *guarded transfer principle*
development: the **transreals**, a four-constructor extension of `ℝ` by two
signed infinities and one exceptional element `null` (Anderson's *nullity* `Φ`).

```
Transreal ::= fin ℝ | pinf | ninf | null
```

Arithmetic is total: every pair of transreals has a sum, a product and a
quotient.  Totality is bought by the exceptional constructor, which absorbs all
the indeterminate forms `∞ - ∞`, `0 · ∞` and `0 / 0`.

The mathematical content of this file is the *exact conservativity* of the
finite fragment: `fin : ℝ → Transreal` is an injection that transports `+`, `*`,
`-` verbatim, and transports `/` verbatim **exactly when the denominator is
nonzero**.  At a vanishing denominator the value leaves the finite fragment, and
*which* exceptional constructor it lands on is dictated by the sign of the
numerator (`Transreal.div_fin_zero`).  That trichotomy is the sharp boundary
exploited by `Cryptography.Transreal.Topology` and
`Cryptography.Transreal.Transfer`.
-/


open Transreal



/-! ### Addition -/








/-! ### Negation -/





/-! ### Multiplication -/













/-! ### Reciprocal and division

The reciprocal of `0` is `pinf`; the reciprocal of either infinity is `0`.
Division is defined, as usual, as multiplication by the reciprocal.  The
resulting behaviour at a vanishing denominator is the trichotomy
`x / 0 = pinf, ninf, null` according as `x > 0`, `x < 0`, `x = 0`. -/



noncomputable instance : Div Transreal := ⟨div⟩





@[simp]

theorem Transreal.fin_div_fin_of_ne{x y : ℝ} (hy : y ≠ 0) :
    fin x / fin y = fin (x / y) := by sorry
