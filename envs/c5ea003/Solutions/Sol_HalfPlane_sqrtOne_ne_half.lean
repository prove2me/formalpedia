-- Prove2me | solution 1 for HalfPlane.sqrtOne_ne_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:45:04.044091+00:00
-- url     : https://prove2.me/submissions/6e37a7bf-753a-4b23-9f16-f6470351ce61

-- Sol generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

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
theorem solution{N u : ℕ} (hN : 3 ≤ N) (hu : u ^ 2 % N = 1 % N) : 2 * u ≠ N := by
  intro hhalf
  have h1N : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1N] at hu
  have hupos : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; simp at hu
    · exact h
  have hdm := Nat.div_add_mod (u ^ 2) N
  obtain ⟨k, hk⟩ : ∃ k, u ^ 2 = N * k + 1 := ⟨u ^ 2 / N, by omega⟩
  have h1 : u ∣ u ^ 2 := ⟨u, by ring⟩
  have h2 : u ∣ N * k := Dvd.dvd.mul_right ⟨2, by omega⟩ k
  have h3 : u ∣ (u ^ 2 - N * k) := Nat.dvd_sub h1 h2
  rw [hk, Nat.add_sub_cancel_left] at h3
  have : u = 1 := Nat.dvd_one.mp h3
  omega
