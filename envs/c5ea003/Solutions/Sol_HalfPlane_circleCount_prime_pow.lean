-- Prove2me | solution 1 for HalfPlane.circleCount_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:40:56.990455+00:00
-- url     : https://prove2.me/submissions/78ff4612-4d46-4dd2-a578-34b56fa4a005

-- Sol generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Theorems.Thm_HalfPlane_circleCount_mul_of_prime_dvd

/-!
# Cycle 5: Hensel lifting for the modular circle

The conic `x² + y² = 1` is smooth over `F_p` for odd `p` (its gradient `(2x, 2y)`
never vanishes on the curve), so every solution modulo `M` lifts to exactly `p`
solutions modulo `pM` whenever `p ∣ M`.  Formally:

* `card_lift_solutions` : a non-degenerate linear congruence in two unknowns over
  `F_p` has exactly `p` solutions;
* `circleCount_mul_of_prime_dvd` : `C(pM) = p·C(M)` for `p` an odd prime dividing `M`;
* `circleCount_prime_pow` : `C(p^k) = p^{k-1}(p - χ_p(-1))`;
* `circleCount_odd` : the completely explicit formula
  `C(N) = ∏_{p ∣ N} p^{v_p(N)-1}(p - χ_p(-1))` for every odd `N ≥ 1`.

This closes the separable baseline: `C` is a closed-form function of the
factorisation of `N`, in stark contrast with the half-plane count `H`, which is not
multiplicative at all.
-/

open HalfPlane

open Finset

/-! ### Counting the lifts -/



/-! ### The lifting criterion -/





/-! ### The lifting bijection -/



/-! ### The prime-power formula -/



/-! ### Lab notes (cycle 5)

```
p^k :  9   27   81   25   125   49   121
C   : 12   36  108   20   100   56   132
p^{k-1}(p ∓ 1) : 3·4  9·4  27·4  5·4  25·4  7·8  11·12
```
-/

example : circleCount 9 = 12 := by decide
example : circleCount 27 = 36 := by decide
example : circleCount 25 = 20 := by decide


open HalfPlane in
theorem solution(p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    ∀ k : ℕ, 1 ≤ k → circleCount (p ^ k) = p ^ (k - 1) * circleCount p := by
  have hp : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hMle : 2 ≤ p ^ n := by
        calc 2 ≤ p := hp
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
      have hdvd : p ∣ p ^ n := dvd_pow_self p (by omega)
      have hstep : circleCount (p ^ (n + 1)) = p * circleCount (p ^ n) := by
        rw [pow_succ, mul_comm (p ^ n) p]
        exact circleCount_mul_of_prime_dvd p (p ^ n) hp2 hMle hdvd
      rw [hstep, ih hn]
      have : n + 1 - 1 = n := by omega
      rw [this]
      have hn1 : n - 1 + 1 = n := by omega
      calc p * (p ^ (n - 1) * circleCount p) = (p ^ (n - 1) * p) * circleCount p := by ring
        _ = p ^ (n - 1 + 1) * circleCount p := by rw [pow_succ]
        _ = p ^ n * circleCount p := by rw [hn1]
