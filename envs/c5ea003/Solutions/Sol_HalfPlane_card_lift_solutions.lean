-- Prove2me | solution 1 for HalfPlane.card_lift_solutions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:33:30.024675+00:00
-- url     : https://prove2.me/submissions/53850150-06ad-459e-8de8-3ddbdb6a0576

-- Sol generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Theorems.Thm_HalfPlane_card_linear_solutions

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
theorem solution(p a b c : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (hab : ¬ (p ∣ a ∧ p ∣ b)) :
    (((Finset.range p) ×ˢ (Finset.range p)).filter
      (fun st => p ∣ (c + 2 * (a * st.1 + b * st.2)))).card = p := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply Ring.two_ne_zero
    rw [ZMod.ringChar_zmod_n p]
    exact_mod_cast hp2
  have hnz : (2 * (a : ZMod p)) ≠ 0 ∨ (2 * (b : ZMod p)) ≠ 0 := by
    rcases not_and_or.mp hab with h | h
    · exact Or.inl (mul_ne_zero h2 (fun hc => h ((ZMod.natCast_eq_zero_iff a p).mp hc)))
    · exact Or.inr (mul_ne_zero h2 (fun hc => h ((ZMod.natCast_eq_zero_iff b p).mp hc)))
  have hbij : (((Finset.range p) ×ˢ (Finset.range p)).filter
      (fun st => p ∣ (c + 2 * (a * st.1 + b * st.2)))).card
      = (Finset.univ.filter (fun st : ZMod p × ZMod p =>
          (2 * (a : ZMod p)) * st.1 + (2 * (b : ZMod p)) * st.2 = -(c : ZMod p))).card := by
    refine Finset.card_bij (fun st _ => ((st.1 : ZMod p), (st.2 : ZMod p))) ?_ ?_ ?_
    · intro st hst
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hst
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hz := (ZMod.natCast_eq_zero_iff (c + 2 * (a * st.1 + b * st.2)) p).mpr hst.2
      push_cast at hz
      linear_combination hz
    · intro s hs t ht hst
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hs ht
      have e1 : (s.1 : ZMod p) = (t.1 : ZMod p) := congrArg Prod.fst hst
      have e2 : (s.2 : ZMod p) = (t.2 : ZMod p) := congrArg Prod.snd hst
      have f1 : s.1 = t.1 := by
        have hv := congrArg ZMod.val e1
        rwa [ZMod.val_natCast_of_lt hs.1.1, ZMod.val_natCast_of_lt ht.1.1] at hv
      have f2 : s.2 = t.2 := by
        have hv := congrArg ZMod.val e2
        rwa [ZMod.val_natCast_of_lt hs.1.2, ZMod.val_natCast_of_lt ht.1.2] at hv
      exact Prod.ext f1 f2
    · intro ST hST
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hST
      refine ⟨(ST.1.val, ST.2.val), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨ZMod.val_lt _, ZMod.val_lt _⟩, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      linear_combination hST
  rw [hbij, card_linear_solutions p _ _ _ hnz]
