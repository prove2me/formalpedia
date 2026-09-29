-- Prove2me | solution 1 for HalfPlane.sqrtOneCount_eq_card_sqrtOneZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:39.803374+00:00
-- url     : https://prove2.me/submissions/751dadb8-32fc-4ba8-89ff-37df3ccd318f

-- Sol generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_circle_cast_iff

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

open HalfPlane

open Finset

/-! ### Square roots of one -/




lemma sq_cast_iff (N a : ℕ) : (a ^ 2 % N = 1 % N) ↔ ((a : ZMod N) ^ 2 = 1) := by
  have h := circle_cast_iff N a 0
  simpa using h








/-! ### The semiprime circle count -/





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

example : circleCount 21 = 21 + 3 + 7 + 1 := by decide
example : sqrtOneCount 21 = sqrtOneCount 3 * sqrtOneCount 7 := by decide
example : 2 * unitRootCount 33 = sqrtOneCount 33 := by decide


open HalfPlane in
theorem solution(N : ℕ) [NeZero N] :
    sqrtOneCount N = (sqrtOneZ N).card := by
  refine Finset.card_bij (fun u _ => (u : ZMod N)) ?_ ?_ ?_
  · intro u hu
    simp only [sqrtOneFinset, Finset.mem_filter, Finset.mem_range] at hu
    simp only [sqrtOneZ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (sq_cast_iff N u).mp hu.2
  · intro u hu v hv huv
    simp only [sqrtOneFinset, Finset.mem_filter, Finset.mem_range] at hu hv
    have := congrArg ZMod.val huv
    rwa [ZMod.val_natCast_of_lt hu.1, ZMod.val_natCast_of_lt hv.1] at this
  · intro u hu
    simp only [sqrtOneZ, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨u.val, ?_, by simp⟩
    simp only [sqrtOneFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt _, by rw [sq_cast_iff]; simpa using hu⟩
