-- Prove2me | Theorems.Thm_PowerSumReveal_lab_note_561_carmichael
-- name    : PowerSumReveal.lab_note_561_carmichael
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:37:39.225391+00:00
-- url     : https://prove2.me/theorems/c31a4c3d-bb55-413c-aabe-dd8aa7377a97
-- title:
--   `N = 561 = 3 · 11 · 17` is squarefree and Korselt, hence the power-sum gcd at the
-- statement:
--   `N = 561 = 3 · 11 · 17` is squarefree and Korselt, hence the power-sum gcd at the
--   natural exponent `k = 560` is trivial: Carmichael numbers are blind spots of the
--   `k = N-1` reveal.
--
--   ```lean
--   theorem PowerSumReveal.lab_note_561_carmichael:
--       Nat.gcd (powerSum 561 560) 561 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumLabNotes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumLabNotes.lean#L154

-- Thm stub generated from Geometry/PowerSumLabNotes.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Definitions.Def_Geometry_PowerSumSquarefree

/-!
# Lab Notes: machine-checked instances of the power-sum reveal

Every statement below is verified twice: once by kernel computation (`decide`) on the
actual definition `powerSum N k = ∑_{a=1}^{N} a^k`, and once by instantiating the
general theorems.  The agreement of the two is the point: it certifies that the
abstract master formula really describes the computed sequence.

Recorded data (computed with `#eval`, then re-proved below):

```
N = 15 = 3*5 ,  λ = lcm(2,4) = 4
k :            1   2   3   4   5   6   7   8   9  10  11  12
gcd(F k, N):  15   5  15   1  15   5  15   1  15   5  15   1

N = 35 = 5*7 ,  λ = lcm(4,6) = 12
k :            1   2   3   4   5   6   7   8   9  10  11  12
gcd(F k, N):  35  35  35   7  35   5  35   7  35  35  35   1

N = 561 = 3*11*17 (Carmichael), λ = lcm(2,10,16) = 80,  80 ∣ 560
gcd(F 560, 561) = 1     -- the reveal is blind at k = N-1 exactly on Korselt numbers
```

## Main results

* `PowerSumReveal.lab_note_15`, `lab_note_35`, `lab_note_77`, `lab_note_143` —
  computed value = theoretical value for four semiprimes.
* `PowerSumReveal.lab_period_table_35` — the full period-12 table, computed.
* `PowerSumReveal.lab_note_large_semiprimes` — reveal values for the four larger test
  semiprimes (221, 323, 667, 8633), obtained from the theorems.
* `PowerSumReveal.lab_note_561_carmichael` — the Korselt bridge on `N = 561`.
-/

open PowerSumReveal

set_option maxRecDepth 100000

/-! ## Small semiprimes: computation versus theory -/





/-! ## The period table -/




/-! ## Larger test semiprimes (theory only — the sums have thousands of digits) -/


/-! ## Density of revealing exponents, checked against the table -/




/-! ## A non-squarefree modulus: one power of `p` is lost -/


/-! ## A Carmichael number defeats the exponent `N - 1` -/

theorem PowerSumReveal.lab_note_561_carmichael:
    Nat.gcd (powerSum 561 560) 561 = 1 := by sorry
