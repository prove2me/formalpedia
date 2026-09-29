-- Prove2me | Definitions.Def_MachineLearning_HalfPlaneSemiprime
-- name    : MachineLearning_HalfPlaneSemiprime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:15:59.241676+00:00
-- url     : https://prove2.me/theorems/375b7cfc-8af1-400f-bee2-e2384d0c396d
-- title:
--   Aether Catalog definitions — MachineLearning_HalfPlaneSemiprime
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HalfPlaneSemiprime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HalfPlaneSemiprime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Theorems.Thm_HalfPlane_circleCount_mul_of_coprime
import Theorems.Thm_HalfPlane_circleCount_prime

/-!
# The correction term is separable, and the semiprime circle count

Cycle 2 of the investigation.  The reflection identity of `HalfPlaneReflection.lean`
writes the non-separable half-plane count as

  `H(N) = high(N) + 2 R(N)`,

with `R(N)` the number of square roots of `1` below `N/2`.  Here we show that the
correction term `R` is itself completely *local*:

* `two_mul_unitRootCount` : `2 R(N) = S(N)` for `N ≥ 3`, where `S(N)` is the total
  number of square roots of `1` modulo `N` (the antipodal pairing `u ↦ N - u` has no
  fixed point on the roots once `N ≥ 3`);
* `sqrtOneCount_mul_of_coprime` : `S` is multiplicative.

So *all* of the non-separability of `H` is carried by the corner count `high`.

We then push the separable side to its arithmetic conclusion:

* `circleCount_semiprime` : `C(pq) = (p - χ_p(-1))(q - χ_q(-1))` for distinct odd
  primes;
* `circleCount_semiprime_three_mod_four` : if `p ≡ q ≡ 3 (mod 4)` then
  `C(pq) = pq + p + q + 1`, hence
* `sum_of_primes_from_circleCount` : `p + q = C(N) - N - 1` — the circle count of a
  Blum-type semiprime *determines the factorisation*.  The obstruction is purely
  computational: evaluating `C(N)` by enumeration costs `Θ(N)` steps.
-/

namespace HalfPlane

open Finset

/-! ### Square roots of one -/

/-- All square roots of `1` modulo `N`, with representatives in `[0,N)`. -/
def sqrtOneFinset (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun u => u ^ 2 % N = 1 % N)

/-- `S(N)`: the number of square roots of `1` modulo `N`. -/
def sqrtOneCount (N : ℕ) : ℕ := (sqrtOneFinset N).card

/-- Square roots of `1` inside `ZMod N`. -/
def sqrtOneZ (N : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.filter (fun u => u ^ 2 = 1)









/-! ### The semiprime circle count -/

/-- The circle count of a product of two distinct odd primes is the product of the
two local conic counts. -/
theorem circleCount_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    circleCount (p * q)
      = (if p % 4 = 1 then p - 1 else p + 1) * (if q % 4 = 1 then q - 1 else q + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [circleCount_mul_of_coprime hcop, circleCount_prime hp2, circleCount_prime hq2]




/-! ### Lab notes (cycle 2)

```
N = p·q   C(N)      N+p+q+1     S(N)  R(N)  H(N)  high(N)
21 = 3·7     32       32          4     2     4      0
33 = 3·11    48       48          4     2     8      4
57 = 3·19    80       80          4     2     8      2
77 = 7·11    96       96          4     2    16      6
35 = 5·7     32   (5 ≡ 1 mod 4)   4     2     6      2
```
The first four rows are Blum semiprimes: `C(N) = N + p + q + 1` exactly.
`S = 2R` in every row, and `S` is multiplicative (`S(21) = S(3)S(7) = 2·2`).
-/

end HalfPlane


