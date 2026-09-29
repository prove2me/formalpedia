-- Prove2me | Definitions.Def_Novelty_MandelbrotDoublingNumberTheory
-- name    : Novelty_MandelbrotDoublingNumberTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:27.028329+00:00
-- url     : https://prove2.me/theorems/48420ace-566a-4ef6-b931-b994f7414750
-- title:
--   Aether Catalog definitions — Novelty_MandelbrotDoublingNumberTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MandelbrotDoublingNumberTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MandelbrotDoublingNumberTheory.lean by skeleton subtraction
import Mathlib

/-!
# The Mandelbrot Set's Secret Number Theory: External Angles and the Doubling Map

The hyperbolic components ("bulbs") of the Mandelbrot set are indexed by rational *external
angles* `p/q ∈ ℚ/ℤ`.  The dynamics on the circle of external angles is the **doubling map**
`θ ↦ 2θ mod 1`.  Restricted to angles with denominator `q`, this is exactly *multiplication by
`2`* on `ℤ/qℤ`.

This file makes the "secret number theory" precise:

* The doubling map on `ℤ/qℤ` is a **bijection iff `q` is odd** (`2` must be invertible), and it
  **fails to be injective when `q` is even**.  Thus the angle `p/q` is periodic under doubling
  exactly when `q` is odd — the classical periodicity criterion for external rays landing on
  Mandelbrot bulbs.
* The `n`-th iterate is multiplication by `2ⁿ`, so the **period of the angle `1/q` equals the
  multiplicative order of `2` modulo `q`** (`orderOf (2 : ZMod q)`); equivalently
  `q ∣ 2^{period} - 1` (a Mersenne-type divisibility).
* For an **odd prime `q`**, Fermat's little theorem forces the bulb period to **divide `q - 1`**.

We close with a *contrarian* section: several natural-looking conjectures about these periods are
**false**, and we prove the counterexamples (e.g. `2` is not a primitive root mod `7`, so the
period is `3`, not `6`).
-/

namespace ExternalAngle

/-- Angle doubling with denominator `q`: on `ℤ/qℤ` it is multiplication by `2`
(the shift `p/q ↦ 2p/q mod 1`). -/
def dbl (q : ℕ) (x : ZMod q) : ZMod q := 2 * x

/-
The `n`-th iterate of the doubling map is multiplication by `2ⁿ`.
-/

/-
**Odd denominators give a bijection.**  When `q` is odd, `2` is a unit mod `q`, so the
doubling map is a bijection: every external angle `p/q` is (purely) periodic.
-/

/-
**Even denominators break injectivity.**  When `q` is even (and positive), the doubling map is
not injective — the corresponding external angles are only *pre*-periodic.
-/

/-
For odd `q`, every point is periodic under the doubling map: there is a common period `n > 0`
with `(dbl q)^[n] = id`.
-/

/-
The period of the angle `1/q` (the point `1`) equals the multiplicative order of `2` mod `q`:
`(dbl q)^[n] 1 = 1 ↔ orderOf (2 : ZMod q) ∣ n`.
-/

/-
**Mersenne-type divisibility.**  The denominator `q` divides `2^{period} - 1`, where
`period = orderOf (2 : ZMod q)`.  For odd `q > 1` this is the genuine Mersenne statement (the
period is a true positive period, cf. `order_two_pos`); for even `q` the order is `0` and the
divisibility holds trivially (`q ∣ 0`).
-/

/-
**Fermat / the bulb-period divides `q - 1`.**  For an odd prime `q`, the period of the `p/q`
bulb (the order of `2` mod `q`) divides `q - 1`.
-/

/-
The period is positive for odd `q > 1` (the order of `2` is a genuine period).
-/

/-! ## Contrarian section: natural conjectures that are FALSE

The following bold guesses about bulb periods are refuted by explicit counterexamples. -/

/-
Concrete order computations (periods of small bulbs).
-/



/-
**Disproof.**  "`2` is always a primitive root modulo every odd prime" (equivalently the
`p/q` bulb always has maximal period `q - 1`).  FALSE: for `q = 7` the period is `3 ≠ 6`.
-/

/-
**Disproof.**  "Every bulb period is prime."  FALSE: for `q = 5` the period is `4`, which is
composite.
-/

end ExternalAngle


