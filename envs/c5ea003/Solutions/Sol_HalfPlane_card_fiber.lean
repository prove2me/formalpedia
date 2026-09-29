-- Prove2me | solution 1 for HalfPlane.card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:36:29.74666+00:00
-- url     : https://prove2.me/submissions/f09558e6-20be-4086-991d-7cf6a3ec97f2

-- Sol generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Theorems.Thm_HalfPlane_card_lift_solutions
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

lemma add_one_mod_iff {n W : ℕ} : (W + 1) % n = 1 % n ↔ n ∣ W := by
  constructor
  · intro h
    have h1 : (W + 1) ≡ (0 + 1) [MOD n] := by simpa [Nat.ModEq] using h
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 h1)
  · intro h
    have h1 : W ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr h
    simpa [Nat.ModEq] using h1.add_right 1

/-- **The Hensel criterion.**  With `a² + b² = Mc + 1` and `p ∣ M`, the lifted point
`(a + sM, b + tM)` lies on the circle modulo `pM` exactly when
`c + 2(as + bt) ≡ 0 (mod p)`. -/
lemma circle_lift_iff {M p a b s t c : ℕ} (hM : 0 < M) (hpM : p ∣ M)
    (hc : a ^ 2 + b ^ 2 = M * c + 1) :
    (((a + s * M) ^ 2 + (b + t * M) ^ 2) % (p * M) = 1 % (p * M))
      ↔ p ∣ (c + 2 * (a * s + b * t)) := by
  have expand : (a + s * M) ^ 2 + (b + t * M) ^ 2
      = M * (c + 2 * (a * s + b * t) + M * (s ^ 2 + t ^ 2)) + 1 := by
    have h0 : (a + s * M) ^ 2 + (b + t * M) ^ 2
        = (a ^ 2 + b ^ 2) + M * (2 * (a * s + b * t) + M * (s ^ 2 + t ^ 2)) := by ring
    rw [h0, hc]; ring
  rw [expand, add_one_mod_iff, show p * M = M * p by ring, Nat.mul_dvd_mul_iff_left hM]
  exact Nat.dvd_add_left (Dvd.dvd.mul_right hpM _)

/-- Every circle point modulo `M ≥ 2` has `a² + b² = Mc + 1` for some `c`. -/
lemma exists_quotient_of_mem_circle {M a b : ℕ} (hM : 2 ≤ M)
    (hc : (a ^ 2 + b ^ 2) % M = 1 % M) : ∃ c, a ^ 2 + b ^ 2 = M * c + 1 := by
  have h1 : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1] at hc
  have hdm := Nat.div_add_mod (a ^ 2 + b ^ 2) M
  exact ⟨(a ^ 2 + b ^ 2) / M, by omega⟩

/-- On the circle modulo `M`, `p ∣ M` implies that `p` cannot divide both coordinates. -/
lemma not_both_dvd {M p a b c : ℕ} (hp : 2 ≤ p) (hpM : p ∣ M)
    (hc : a ^ 2 + b ^ 2 = M * c + 1) : ¬ (p ∣ a ∧ p ∣ b) := by
  rintro ⟨ha, hb⟩
  have h1 : p ∣ a ^ 2 + b ^ 2 := Nat.dvd_add (Dvd.dvd.pow ha (by norm_num))
    (Dvd.dvd.pow hb (by norm_num))
  rw [hc] at h1
  have h2 : p ∣ M * c := Dvd.dvd.mul_right hpM c
  have : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
  have := Nat.le_of_dvd (by norm_num) this
  omega

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
theorem solution(p M a b : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hM : 2 ≤ M)
    (hpM : p ∣ M) (ha : a < M) (hb : b < M) (hcirc : (a ^ 2 + b ^ 2) % M = 1 % M) :
    ((circleFinset (p * M)).filter (fun q => (q.1 % M, q.2 % M) = (a, b))).card = p := by
  classical
  have hp : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  obtain ⟨c, hc⟩ := exists_quotient_of_mem_circle hM hcirc
  have hab := not_both_dvd hp hpM hc
  have hM0 : 0 < M := by omega
  have hbij : ((circleFinset (p * M)).filter (fun q => (q.1 % M, q.2 % M) = (a, b))).card
      = (((Finset.range p) ×ˢ (Finset.range p)).filter
          (fun st => p ∣ (c + 2 * (a * st.1 + b * st.2)))).card := by
    refine Finset.card_bij' (fun q _ => (q.1 / M, q.2 / M))
      (fun st _ => (a + st.1 * M, b + st.2 * M)) ?_ ?_ ?_ ?_
    · -- forward map lands in the solution set
      intro q hq
      simp only [Finset.mem_filter, mem_circleFinset, Prod.mk.injEq] at hq
      obtain ⟨⟨h1, h2, hcq⟩, hr1, hr2⟩ := hq
      have hd1 : q.1 = a + (q.1 / M) * M := by
        calc q.1 = M * (q.1 / M) + q.1 % M := (Nat.div_add_mod _ _).symm
          _ = a + (q.1 / M) * M := by rw [hr1]; ring
      have hd2 : q.2 = b + (q.2 / M) * M := by
        calc q.2 = M * (q.2 / M) + q.2 % M := (Nat.div_add_mod _ _).symm
          _ = b + (q.2 / M) * M := by rw [hr2]; ring
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Nat.div_lt_of_lt_mul (by rw [mul_comm] at h1; exact h1)
      · exact Nat.div_lt_of_lt_mul (by rw [mul_comm] at h2; exact h2)
      · rw [← circle_lift_iff (s := q.1 / M) (t := q.2 / M) hM0 hpM hc]
        rw [← hd1, ← hd2]
        exact hcq
    · -- backward map lands in the fiber
      intro st hst
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hst
      obtain ⟨⟨hs1, hs2⟩, hcond⟩ := hst
      have hlt1 : a + st.1 * M < p * M := by
        calc a + st.1 * M < M + st.1 * M := by omega
          _ = (st.1 + 1) * M := by ring
          _ ≤ p * M := Nat.mul_le_mul_right M (by omega)
      have hlt2 : b + st.2 * M < p * M := by
        calc b + st.2 * M < M + st.2 * M := by omega
          _ = (st.2 + 1) * M := by ring
          _ ≤ p * M := Nat.mul_le_mul_right M (by omega)
      simp only [Finset.mem_filter, mem_circleFinset, Prod.mk.injEq]
      refine ⟨⟨hlt1, hlt2, ?_⟩, ?_, ?_⟩
      · rw [circle_lift_iff hM0 hpM hc]
        exact hcond
      · show (a + st.1 * M) % M = a
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
      · show (b + st.2 * M) % M = b
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    · -- left inverse
      intro q hq
      simp only [Finset.mem_filter, mem_circleFinset, Prod.mk.injEq] at hq
      obtain ⟨⟨h1, h2, hcq⟩, hr1, hr2⟩ := hq
      have hd1 : q.1 = a + (q.1 / M) * M := by
        calc q.1 = M * (q.1 / M) + q.1 % M := (Nat.div_add_mod _ _).symm
          _ = a + (q.1 / M) * M := by rw [hr1]; ring
      have hd2 : q.2 = b + (q.2 / M) * M := by
        calc q.2 = M * (q.2 / M) + q.2 % M := (Nat.div_add_mod _ _).symm
          _ = b + (q.2 / M) * M := by rw [hr2]; ring
      exact Prod.ext hd1.symm hd2.symm
    · -- right inverse
      intro st hst
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hst
      have e1 : (a + st.1 * M) / M = st.1 := by
        rw [Nat.add_mul_div_right _ _ hM0, Nat.div_eq_of_lt ha, Nat.zero_add]
      have e2 : (b + st.2 * M) / M = st.2 := by
        rw [Nat.add_mul_div_right _ _ hM0, Nat.div_eq_of_lt hb, Nat.zero_add]
      exact Prod.ext e1 e2
  rw [hbij, card_lift_solutions p a b c hp2 hab]
