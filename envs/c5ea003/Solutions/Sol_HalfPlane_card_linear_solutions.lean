-- Prove2me | solution 1 for HalfPlane.card_linear_solutions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:31:58.453305+00:00
-- url     : https://prove2.me/submissions/86f8335c-327f-4361-9c85-179202034563

-- Sol generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneClosedForm

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
theorem solution(p : ℕ) [Fact (Nat.Prime p)] (α β γ : ZMod p)
    (h : α ≠ 0 ∨ β ≠ 0) :
    (Finset.univ.filter (fun st : ZMod p × ZMod p => α * st.1 + β * st.2 = γ)).card = p := by
  classical
  rcases h with ha | hb
  · have hcard : (Finset.univ.filter (fun st : ZMod p × ZMod p => α * st.1 + β * st.2 = γ)).card
        = (Finset.univ : Finset (ZMod p)).card := by
      refine Finset.card_bij (fun st _ => st.2) (fun st _ => Finset.mem_univ _) ?_ ?_
      · intro s hs t ht hst
        simp only [Finset.mem_filter] at hs ht
        have h2 : s.2 = t.2 := hst
        have h1 : α * s.1 = α * t.1 := by linear_combination hs.2 - ht.2 - β * h2
        exact Prod.ext (mul_left_cancel₀ ha h1) h2
      · intro b _
        refine ⟨((γ - β * b) / α, b), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        field_simp
        ring
    rw [hcard]; simp [ZMod.card p]
  · have hcard : (Finset.univ.filter (fun st : ZMod p × ZMod p => α * st.1 + β * st.2 = γ)).card
        = (Finset.univ : Finset (ZMod p)).card := by
      refine Finset.card_bij (fun st _ => st.1) (fun st _ => Finset.mem_univ _) ?_ ?_
      · intro s hs t ht hst
        simp only [Finset.mem_filter] at hs ht
        have h1 : s.1 = t.1 := hst
        have h2 : β * s.2 = β * t.2 := by linear_combination hs.2 - ht.2 - α * h1
        exact Prod.ext h1 (mul_left_cancel₀ hb h2)
      · intro a _
        refine ⟨(a, (γ - α * a) / β), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        field_simp
        ring
    rw [hcard]; simp [ZMod.card p]
