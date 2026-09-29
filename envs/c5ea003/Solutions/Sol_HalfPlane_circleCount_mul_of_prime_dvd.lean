-- Prove2me | solution 1 for HalfPlane.circleCount_mul_of_prime_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:38:49.629722+00:00
-- url     : https://prove2.me/submissions/ecf73256-1880-4ffc-bf66-37947390f4b3

-- Sol generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Theorems.Thm_HalfPlane_card_fiber
import Theorems.Thm_HalfPlane_mem_circleFinset

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
theorem solution(p M : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (hM : 2 ≤ M) (hpM : p ∣ M) :
    circleCount (p * M) = p * circleCount M := by
  classical
  have hM0 : 0 < M := by omega
  have hmaps : ∀ q ∈ circleFinset (p * M), ((q.1 % M, q.2 % M) : ℕ × ℕ) ∈ circleFinset M := by
    intro q hq
    rw [mem_circleFinset] at hq ⊢
    obtain ⟨h1, h2, hc⟩ := hq
    refine ⟨Nat.mod_lt _ hM0, Nat.mod_lt _ hM0, ?_⟩
    have hmod : (q.1 % M) ^ 2 + (q.2 % M) ^ 2 ≡ q.1 ^ 2 + q.2 ^ 2 [MOD M] :=
      Nat.ModEq.add (Nat.ModEq.pow 2 (Nat.mod_modEq _ _)) (Nat.ModEq.pow 2 (Nat.mod_modEq _ _))
    have hdvd : M ∣ p * M := ⟨p, by ring⟩
    have h3 : q.1 ^ 2 + q.2 ^ 2 ≡ 1 [MOD M] := Nat.ModEq.of_dvd hdvd hc
    exact hmod.trans h3
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [circleCount, hsum]
  have hconst : ∀ ab ∈ circleFinset M,
      ((circleFinset (p * M)).filter (fun q => (q.1 % M, q.2 % M) = ab)).card = p := by
    intro ab hab
    rw [mem_circleFinset] at hab
    obtain ⟨h1, h2, hc⟩ := hab
    have := card_fiber p M ab.1 ab.2 hp2 hM hpM h1 h2 hc
    simpa using this
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, circleCount, mul_comm]
