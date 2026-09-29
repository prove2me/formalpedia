-- Prove2me | solution 1 for Transreal.mul_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:17:16.367101+00:00
-- url     : https://prove2.me/submissions/b4abf882-359f-47ce-8d0b-f2f67d0b4f07

-- Sol generated from Cryptography/Transreal/Core.lean
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










theorem Transreal_mul_comm (a b : Transreal) : a * b = b * a := by
  cases a <;> cases b <;> try rfl
  exact congrArg fin (_root_.mul_comm _ _)

@[simp] theorem fin_one_mul (a : Transreal) : fin 1 * a = a := by
  cases a with
  | fin x => exact congrArg fin (one_mul x)
  | pinf => show mul _ _ = _; simp [mul]
  | ninf => show mul _ _ = _; simp [mul]
  | null => rfl


/-! ### Reciprocal and division

The reciprocal of `0` is `pinf`; the reciprocal of either infinity is `0`.
Division is defined, as usual, as multiplication by the reciprocal.  The
resulting behaviour at a vanishing denominator is the trichotomy
`x / 0 = pinf, ninf, null` according as `x > 0`, `x < 0`, `x = 0`. -/



noncomputable instance : Div Transreal := ⟨div⟩











/-! ### Structure of the finite fragment -/








/-! ### Lifting real functions -/





open Transreal in
@[simp] theorem solution(a : Transreal) : a * fin 1 = a := by
  rw [Transreal_mul_comm]; simp
