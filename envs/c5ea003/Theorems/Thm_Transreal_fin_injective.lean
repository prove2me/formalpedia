-- Prove2me | Theorems.Thm_Transreal_fin_injective
-- name    : Transreal.fin_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:50.202063+00:00
-- url     : https://prove2.me/theorems/1c5f8d58-1fe4-4c9a-8e63-14dc8ac57784
-- title:
--   `fin` is injective: the finite fragment is a faithful copy of `ℝ`.
-- statement:
--   `fin` is injective: the finite fragment is a faithful copy of `ℝ`.
--
--   ```lean
--   theorem Transreal.fin_injective: Function.Injective fin := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/Transreal/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/Transreal/Core.lean#L36

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

theorem Transreal.fin_injective: Function.Injective fin := by sorry
