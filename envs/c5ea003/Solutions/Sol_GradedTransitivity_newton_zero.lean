-- Prove2me | solution 1 for GradedTransitivity.newton_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:45:06.792405+00:00
-- url     : https://prove2.me/submissions/8f99fdf5-7302-46d5-9f3c-fd95703c5091

-- Sol generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure

/-!
# Newton's forward-difference classification

This file closes the circle around the rationality criterion by proving the
missing *converse*: a sequence whose `k`-th forward difference vanishes
eventually is, from that point on, a `ℚ`-linear combination of the `k`
binomial functions `n ↦ C(n-N, j)`, `j < k` (Newton's forward difference
formula).  Together with `FiniteDifference` this yields the classification

`(1-q)^k` clears `∑ a n qⁿ`
  ⟺ `Δ^k a` vanishes eventually
  ⟺ `a` is eventually a combination of `C(·-N, j)`, `j < k`.

For a graded `G`-set this says: eventual `r`-transitivity is only the simplest
member of a hierarchy, and the exponent `k` in the denominator measures exactly
the binomial degree of the orbit-counting sequence.

## Main results

* `newton_forward` : Newton's forward difference formula.
* `sdiff_iter_binom_eq_zero` : the binomial functions are annihilated.
* `rationality_tfae_newton` : the three-way classification.
-/

open GradedTransitivity

open Polynomial

/-! ### Linearity of the difference operator -/




/-! ### The shifted binomial functions -/





/-! ### Newton's forward difference formula -/


/-- Hockey-stick identity, in the form needed here. -/
theorem sum_range_choose_hockey (j : ℕ) :
    ∀ m : ℕ, ∑ i ∈ Finset.range m, ((i.choose j : ℚ)) = (m.choose (j + 1) : ℚ) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' m j]
      push_cast
      ring



/-! ### The classification -/



open GradedTransitivity in
theorem solution:
    ∀ (k : ℕ) (b : ℕ → ℚ), (∀ m, sdiff^[k] b m = 0) →
      ∀ m, b m = ∑ j ∈ Finset.range k, (sdiff^[j] b 0) * (m.choose j : ℚ) := by
  intro k
  induction k with
  | zero => intro b hb m; simpa using hb m
  | succ k ih =>
      intro b hb m
      have hc : ∀ i, sdiff^[k] (sdiff b) i = 0 := by
        intro i
        rw [← Function.iterate_succ_apply]
        exact hb i
      have hcform := ih (sdiff b) hc
      have htel : ∑ i ∈ Finset.range m, sdiff b i = b m - b 0 :=
        Finset.sum_range_sub (fun i => b i) m
      have hexp : ∑ i ∈ Finset.range m, sdiff b i
          = ∑ j ∈ Finset.range k, (sdiff^[j] (sdiff b) 0) * ((m.choose (j + 1) : ℚ)) := by
        calc ∑ i ∈ Finset.range m, sdiff b i
            = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range k,
                (sdiff^[j] (sdiff b) 0) * ((i.choose j : ℚ)) := by
              exact Finset.sum_congr rfl (fun i _ => hcform i)
          _ = ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range m,
                (sdiff^[j] (sdiff b) 0) * ((i.choose j : ℚ)) := Finset.sum_comm
          _ = ∑ j ∈ Finset.range k, (sdiff^[j] (sdiff b) 0) * ((m.choose (j + 1) : ℚ)) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [← Finset.mul_sum, sum_range_choose_hockey j m]
      rw [Finset.sum_range_succ']
      have hb0 : ∀ j, sdiff^[j + 1] b 0 = sdiff^[j] (sdiff b) 0 := by
        intro j; rw [Function.iterate_succ_apply]
      have : b m = b 0 + ∑ i ∈ Finset.range m, sdiff b i := by rw [htel]; ring
      rw [this, hexp]
      simp only [hb0, Function.iterate_zero, id_eq, Nat.choose_zero_right, Nat.cast_one, mul_one]
      ring
