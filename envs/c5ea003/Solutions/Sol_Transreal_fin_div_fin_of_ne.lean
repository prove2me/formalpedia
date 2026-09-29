-- Prove2me | solution 1 for Transreal.fin_div_fin_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:15:14.68954+00:00
-- url     : https://prove2.me/submissions/3d020f5e-c662-4252-b1ec-c1349abbfcc0

-- Sol generated from Cryptography/Transreal/Core.lean
import Mathlib
import Definitions.Def_Cryptography_Transreal_Core
import Theorems.Thm_Transreal_fin_mul_fin

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

theorem div_def (a b : Transreal) : a / b = a * recip b := rfl


theorem recip_fin_of_ne {x : ℝ} (hx : x ≠ 0) : recip (fin x) = fin x⁻¹ := by
  simp [recip, hx]








/-! ### Structure of the finite fragment -/








/-! ### Lifting real functions -/





open Transreal in
@[simp] theorem solution{x y : ℝ} (hy : y ≠ 0) :
    fin x / fin y = fin (x / y) := by
  rw [div_def, recip_fin_of_ne hy, fin_mul_fin, div_eq_mul_inv]
