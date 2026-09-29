-- Prove2me | solution 1 for HalfPlane.sqrtOneCount_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:45:01.613828+00:00
-- url     : https://prove2.me/submissions/2a5e1b53-10b9-45cd-b5e7-04e6f6d4d374

-- Sol generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_sqrtOneCount_eq_card_sqrtOneZ

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
theorem solution{m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    sqrtOneCount (m * n) = sqrtOneCount m * sqrtOneCount n := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [sqrtOneCount_eq_card_sqrtOneZ, sqrtOneCount_eq_card_sqrtOneZ,
    sqrtOneCount_eq_card_sqrtOneZ, ← Finset.card_product]
  set e := ZMod.chineseRemainder h with he
  refine Finset.card_bij (fun u _ => ((e u).1, (e u).2)) ?_ ?_ ?_
  · intro u hu
    simp only [sqrtOneZ, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hmap : (e u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
    simp only [Finset.mem_product, sqrtOneZ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
  · intro u _ v _ huv
    have : e u = e v := Prod.ext (congrArg Prod.fst huv) (congrArg Prod.snd huv)
    exact e.injective this
  · intro b hb
    simp only [Finset.mem_product, sqrtOneZ, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    refine ⟨e.symm (b.1, b.2), ?_, by simp⟩
    simp only [sqrtOneZ, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← map_pow]
    have : ((b.1, b.2) : ZMod m × ZMod n) ^ 2 = 1 :=
      Prod.ext (by simpa using hb.1) (by simpa using hb.2)
    rw [this, map_one]
