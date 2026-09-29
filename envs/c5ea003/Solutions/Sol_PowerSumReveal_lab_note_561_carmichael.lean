-- Prove2me | solution 1 for PowerSumReveal.lab_note_561_carmichael
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:13.75871+00:00
-- url     : https://prove2.me/submissions/b4c89a9c-298a-42f5-89ec-4239b8bf6462

-- Sol generated from Geometry/PowerSumLabNotes.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Definitions.Def_Geometry_PowerSumSquarefree
import Theorems.Thm_PowerSumReveal_korselt_iff_coprime_powerSum

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



open PowerSumReveal in
theorem solution:
    Nat.gcd (powerSum 561 560) 561 = 1 := by
  have p3 : Nat.Prime 3 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  have p17 : Nat.Prime 17 := by norm_num
  have hsq : Squarefree 561 := by
    have h : (561 : ℕ) = 3 * (11 * 17) := by norm_num
    rw [h]
    refine Nat.squarefree_mul_iff.2 ⟨by norm_num, p3.squarefree, ?_⟩
    exact Nat.squarefree_mul_iff.2 ⟨by norm_num, p11.squarefree, p17.squarefree⟩
  refine (korselt_iff_coprime_powerSum hsq (by norm_num)).1 ?_
  intro r hr
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.1 hr
  have hmem : r ∈ Nat.divisors 561 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 561 = {1, 3, 11, 17, 33, 51, 187, 561} := by decide
  rw [hdiv] at hmem
  clear hr hdvd
  fin_cases hmem <;> first
    | decide
    | exact absurd hprime (by norm_num)
