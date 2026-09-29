-- Prove2me | Definitions.Def_Cryptography_Transreal_Core
-- name    : Cryptography_Transreal_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:24:14.564308+00:00
-- url     : https://prove2.me/theorems/4b002da6-cdd5-4242-bb90-4cd59d480b35
-- title:
--   Aether Catalog definitions — Cryptography_Transreal_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Transreal.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Transreal/Core.lean by skeleton subtraction
import Mathlib

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

/-- The transreal carrier: the reals, two signed infinities, and nullity. -/
inductive Transreal : Type
  | fin (x : ℝ) : Transreal
  | pinf : Transreal
  | ninf : Transreal
  | null : Transreal

namespace Transreal



/-! ### Addition -/

/-- Transreal addition.  `null` is absorbing and `pinf + ninf = null`. -/
def add : Transreal → Transreal → Transreal
  | null, _ => null
  | _, null => null
  | fin x, fin y => fin (x + y)
  | fin _, pinf => pinf
  | fin _, ninf => ninf
  | pinf, fin _ => pinf
  | ninf, fin _ => ninf
  | pinf, pinf => pinf
  | ninf, ninf => ninf
  | pinf, ninf => null
  | ninf, pinf => null

instance : Add Transreal := ⟨add⟩






/-! ### Negation -/

/-- Transreal negation; it swaps the two infinities and fixes nullity. -/
def neg : Transreal → Transreal
  | fin x => fin (-x)
  | pinf => ninf
  | ninf => pinf
  | null => null

instance : Neg Transreal := ⟨neg⟩



/-! ### Multiplication -/

open Classical in
/-- Transreal multiplication.  `null` is absorbing and `0 · ∞ = null`. -/
noncomputable def mul : Transreal → Transreal → Transreal
  | null, _ => null
  | _, null => null
  | fin x, fin y => fin (x * y)
  | fin x, pinf => if x = 0 then null else if 0 < x then pinf else ninf
  | fin x, ninf => if x = 0 then null else if 0 < x then ninf else pinf
  | pinf, fin y => if y = 0 then null else if 0 < y then pinf else ninf
  | ninf, fin y => if y = 0 then null else if 0 < y then ninf else pinf
  | pinf, pinf => pinf
  | pinf, ninf => ninf
  | ninf, pinf => ninf
  | ninf, ninf => pinf

noncomputable instance : Mul Transreal := ⟨mul⟩











/-! ### Reciprocal and division

The reciprocal of `0` is `pinf`; the reciprocal of either infinity is `0`.
Division is defined, as usual, as multiplication by the reciprocal.  The
resulting behaviour at a vanishing denominator is the trichotomy
`x / 0 = pinf, ninf, null` according as `x > 0`, `x < 0`, `x = 0`. -/

open Classical in
/-- Transreal reciprocal. -/
noncomputable def recip : Transreal → Transreal
  | fin x => if x = 0 then pinf else fin x⁻¹
  | pinf => fin 0
  | ninf => fin 0
  | null => null

/-- Transreal division. -/
noncomputable def div (a b : Transreal) : Transreal := a * recip b

noncomputable instance : Div Transreal := ⟨div⟩











/-! ### Structure of the finite fragment -/

/-- The finite fragment, i.e. the image of `ℝ`. -/
def Finite (a : Transreal) : Prop := ∃ x : ℝ, a = fin x







/-! ### Lifting real functions -/

/-- The strict lift of a real function to the transreals: it acts as `f` on the
finite fragment and sends every exceptional element to `null`. -/
def lift (f : ℝ → ℝ) : Transreal → Transreal
  | fin x => fin (f x)
  | _ => null



end Transreal


