-- Prove2me | solution 1 for Transreal.zero_div_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:18:30.21765+00:00
-- url     : https://prove2.me/submissions/02ebf53e-c0a7-4843-8ffb-79933a85aeda

-- Sol generated from Cryptography/Transreal/Core.lean
import Mathlib
import Definitions.Def_Cryptography_Transreal_Core
import Theorems.Thm_Transreal_fin_zero_mul_pinf

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






theorem fin_mul_pinf_of_pos {x : ℝ} (hx : 0 < x) : fin x * pinf = pinf := by
  show mul _ _ = _; simp [mul, hx.ne', hx]

theorem fin_mul_pinf_of_neg {x : ℝ} (hx : x < 0) : fin x * pinf = ninf := by
  show mul _ _ = _; simp [mul, hx.ne, asymm hx]






/-! ### Reciprocal and division

The reciprocal of `0` is `pinf`; the reciprocal of either infinity is `0`.
Division is defined, as usual, as multiplication by the reciprocal.  The
resulting behaviour at a vanishing denominator is the trichotomy
`x / 0 = pinf, ninf, null` according as `x > 0`, `x < 0`, `x = 0`. -/



noncomputable instance : Div Transreal := ⟨div⟩

theorem div_def (a b : Transreal) : a / b = a * recip b := rfl

@[simp] theorem recip_fin_zero : recip (fin 0) = pinf := by simp [recip]




/-- **The division boundary.**  At a vanishing denominator the quotient leaves
the finite fragment, and *which* exceptional constructor it lands on is
determined by the sign of the numerator. -/
theorem div_fin_zero (x : ℝ) :
    fin x / fin 0 = if x = 0 then null else if 0 < x then pinf else ninf := by
  rw [div_def, recip_fin_zero]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [fin_mul_pinf_of_neg h]; simp [h.ne, asymm h]
  · subst h; simp
  · rw [fin_mul_pinf_of_pos h]; simp [h.ne', h]





/-! ### Structure of the finite fragment -/








/-! ### Lifting real functions -/





open Transreal in
@[simp] theorem solution: fin 0 / fin 0 = null := by simp [div_fin_zero]
