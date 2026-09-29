-- Prove2me | Theorems.Thm_ExternalAngle_dbl_bijective_of_odd
-- name    : ExternalAngle.dbl_bijective_of_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:48:23.727253+00:00
-- url     : https://prove2.me/theorems/a051494d-59c7-4a8f-af6e-51220744fc5d
-- title:
--   Dbl bijective of odd
-- statement:
--   Formal statement of `ExternalAngle.dbl_bijective_of_odd` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ExternalAngle.dbl_bijective_of_odd{q : ℕ} (hq : Odd q) : Function.Bijective (dbl q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MandelbrotDoublingNumberTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MandelbrotDoublingNumberTheory.lean#L43

-- Thm stub generated from Novelty/MandelbrotDoublingNumberTheory.lean
import Mathlib
import Definitions.Def_Novelty_MandelbrotDoublingNumberTheory

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

open ExternalAngle


/-
The `n`-th iterate of the doubling map is multiplication by `2ⁿ`.
-/

/-
**Odd denominators give a bijection.**  When `q` is odd, `2` is a unit mod `q`, so the
doubling map is a bijection: every external angle `p/q` is (purely) periodic.
-/

theorem ExternalAngle.dbl_bijective_of_odd{q : ℕ} (hq : Odd q) : Function.Bijective (dbl q) := by sorry
