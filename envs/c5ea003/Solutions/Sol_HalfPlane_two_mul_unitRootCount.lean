-- Prove2me | solution 1 for HalfPlane.two_mul_unitRootCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:47:09.133869+00:00
-- url     : https://prove2.me/submissions/830331a8-e5e5-4c07-a61e-452d68cb1896

-- Sol generated from MachineLearning/HalfPlaneSemiprime.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_circle_reflect_fst
import Theorems.Thm_HalfPlane_sqrtOne_ne_half
import Theorems.Thm_HalfPlane_unitRootCount_eq_card

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







/-- Zero is not a square root of `1` modulo `N` when `N ≥ 2`. -/
lemma sqrtOne_pos {N u : ℕ} (hN : 2 ≤ N) (hu : u ^ 2 % N = 1 % N) : 1 ≤ u := by
  rcases Nat.eq_zero_or_pos u with h | h
  · subst h
    rw [Nat.mod_eq_of_lt (show 1 < N by omega)] at hu
    simp at hu
  · exact h





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
theorem solution(N : ℕ) (hN : 3 ≤ N) :
    2 * unitRootCount N = sqrtOneCount N := by
  haveI : NeZero N := ⟨by omega⟩
  have hlow : unitRootFinset N = (sqrtOneFinset N).filter (fun u => 2 * u < N) := by
    ext u
    simp only [unitRootFinset, sqrtOneFinset, Finset.mem_filter, Finset.mem_range]
    tauto
  have hhigh : ((sqrtOneFinset N).filter (fun u => ¬ 2 * u < N)).card
      = (unitRootFinset N).card := by
    refine Finset.card_bij' (fun u _ => N - u) (fun u _ => N - u) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, sqrtOneFinset, Finset.mem_range] at hu
      obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hu
      have hne := sqrtOne_ne_half hN hu2
      simp only [unitRootFinset, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ?_⟩
      have := (circle_reflect_fst (N := N) (a := u) (b := 0) (by omega)).mpr (by simpa using hu2)
      simpa using this
    · intro u hu
      simp only [unitRootFinset, Finset.mem_filter, Finset.mem_range] at hu
      obtain ⟨hu1, hu2, hu3⟩ := hu
      have hne := sqrtOne_ne_half hN hu3
      have hpos := sqrtOne_pos (by omega) hu3
      simp only [Finset.mem_filter, sqrtOneFinset, Finset.mem_range]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      have := (circle_reflect_fst (N := N) (a := u) (b := 0) (by omega)).mpr (by simpa using hu3)
      simpa using this
    · intro u hu
      simp only [Finset.mem_filter, sqrtOneFinset, Finset.mem_range] at hu
      show N - (N - u) = u
      omega
    · intro u hu
      simp only [unitRootFinset, Finset.mem_filter, Finset.mem_range] at hu
      show N - (N - u) = u
      omega
  have hsplit : ((sqrtOneFinset N).filter (fun u => 2 * u < N)).card
      + ((sqrtOneFinset N).filter (fun u => ¬ 2 * u < N)).card = (sqrtOneFinset N).card :=
    Finset.card_filter_add_card_filter_not (s := sqrtOneFinset N) (p := fun u => 2 * u < N)
  have hpair : ((sqrtOneFinset N).filter (fun u => ¬ 2 * u < N)).card
      = ((sqrtOneFinset N).filter (fun u => 2 * u < N)).card := by rw [hhigh, hlow]
  rw [unitRootCount_eq_card, hlow]
  simp only [sqrtOneCount]
  rw [← hsplit, hpair]
  ring
