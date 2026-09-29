-- Prove2me | solution 1 for HalfPlane.card_circleZ_erase
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:51:20.57002+00:00
-- url     : https://prove2.me/submissions/7fa043a7-b647-4c32-bf90-3e9ef8e72e0b

-- Sol generated from MachineLearning/HalfPlaneCRTSeparable.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Theorems.Thm_HalfPlane_mem_circleZ

/-!
# The circle count is CRT-separable

The modular circle `x² + y² ≡ 1 (mod N)` is a *local* object: its point count
splits as a product over coprime factorisations,

  `C(m n) = C(m) · C(n)`  for `gcd(m,n) = 1`,

and at an odd prime it is given by the classical conic count

  `C(p) = p - χ(-1) = p - 1` if `p ≡ 1 (mod 4)`, `p + 1` if `p ≡ 3 (mod 4)`.

The proof of the prime formula is by the stereographic parametrisation of the
conic from the point `(-1, 0)`: the circle minus that point is in bijection with
the set of slopes `t` for which `1 + t² ≠ 0`.

This is the "CRT-separable" baseline against which the half-plane count
`H(N)` of `HalfPlaneReflection.lean` is measured.
-/

open HalfPlane

open Finset


variable {m n : ℕ} [NeZero m] [NeZero n]





variable (p : ℕ) [Fact (Nat.Prime p)]


variable {p}


lemma two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n p]
  exact_mod_cast hp

/-- On the circle, the only point with `x = -1` is `(-1, 0)`; hence away from it the
stereographic denominator `1 + x` is invertible. -/
lemma one_add_fst_ne_zero {q : ZMod p × ZMod p}
    (hq : q ∈ (circleZ p).erase ((-1 : ZMod p), (0 : ZMod p))) : (1 : ZMod p) + q.1 ≠ 0 := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
  rw [mem_circleZ] at hmem
  intro h
  have hx1 : q.1 = -1 := by linear_combination h
  have hy : q.2 ^ 2 = 0 := by rw [hx1] at hmem; linear_combination hmem
  exact hne (Prod.ext hx1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy))

/-- The stereographic slope `t = y/(1+x)` satisfies `1 + t² = 2/(1+x)`. -/
lemma denom_eq {x y : ZMod p} (h : x ^ 2 + y ^ 2 = 1) (hx : (1 : ZMod p) + x ≠ 0) :
    1 + (y / (1 + x)) ^ 2 = 2 / (1 + x) := by
  field_simp
  linear_combination h







open HalfPlane in
theorem solution(hp : p ≠ 2) :
    ((circleZ p).erase ((-1 : ZMod p), (0 : ZMod p))).card = (slopeSet p).card := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  refine Finset.card_bij'
    (fun q _ => q.2 / (1 + q.1))
    (fun u _ => ((1 - u ^ 2) / (1 + u ^ 2), 2 * u / (1 + u ^ 2)))
    ?_ ?_ ?_ ?_
  · intro q hq
    have hx := one_add_fst_ne_zero hq
    have hmem := mem_circleZ.mp (Finset.mem_of_mem_erase hq)
    simp only [slopeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [denom_eq hmem hx]
    exact div_ne_zero h2 hx
  · intro u hu
    simp only [slopeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hcon
      have hx : (1 - u ^ 2) / (1 + u ^ 2) = -1 := congrArg Prod.fst hcon
      rw [div_eq_iff hu] at hx
      exact h2 (by linear_combination hx)
    · rw [mem_circleZ]
      simp only
      field_simp
      ring
  · intro q hq
    have hx := one_add_fst_ne_zero hq
    have hmem := mem_circleZ.mp (Finset.mem_of_mem_erase hq)
    have hd := denom_eq hmem hx
    simp only
    rw [hd]
    refine Prod.ext ?_ ?_
    · simp only
      rw [div_div_eq_mul_div, div_eq_iff h2]
      field_simp
      linear_combination -hmem
    · simp only
      rw [div_div_eq_mul_div, div_eq_iff h2]
      field_simp
  · intro u hu
    simp only [slopeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hden : (1 : ZMod p) + (1 - u ^ 2) / (1 + u ^ 2) = 2 / (1 + u ^ 2) := by
      field_simp
      ring
    simp only
    rw [hden, div_div_eq_mul_div, div_eq_iff h2]
    field_simp
