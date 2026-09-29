-- Prove2me | Theorems.Thm_Transreal_mul_null
-- name    : Transreal.mul_null
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:03:32.038651+00:00
-- url     : https://prove2.me/theorems/7cfa96e6-f88e-4e93-b066-4887cbbb3cb5
-- title:
--   Mul null
-- statement:
--   Formal statement of `Transreal.mul_null` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Transreal.mul_null(a : Transreal) : a * null = null := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/Transreal/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/Transreal/Core.lean#L126

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



@[simp]

theorem Transreal.mul_null(a : Transreal) : a * null = null := by sorry
