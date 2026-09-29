-- Prove2me | Theorems.Thm_Transreal_lift_fin
-- name    : Transreal.lift_fin
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:30.592737+00:00
-- url     : https://prove2.me/theorems/776c0692-8e8b-45a2-9a46-9f10b00e0b3e
-- title:
--   Lift fin
-- statement:
--   Formal statement of `Transreal.lift_fin` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Transreal.lift_fin(f : ℝ → ℝ) (x : ℝ) : lift f (fin x) = fin (f x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/Transreal/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/Transreal/Core.lean#L269

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











/-! ### Structure of the finite fragment -/








/-! ### Lifting real functions -/


@[simp]

theorem Transreal.lift_fin(f : ℝ → ℝ) (x : ℝ) : lift f (fin x) = fin (f x) := by sorry
