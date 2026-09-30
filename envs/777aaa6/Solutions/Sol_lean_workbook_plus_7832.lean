-- Prove2me | solution 1 for lean_workbook_plus_7832
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:35:59.69604+00:00
-- url     : https://prove2.me/submissions/7910f09a-2a07-4b36-add0-418af9e71c9e

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Iterate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem inverse_average_second_difference {f : ℝ → ℝ}
    (hBij : Function.Bijective f)
    (hSum : ∀ x, f x + Function.invFun f x = 2 * x) :
    ∀ x, f (f x) = 2 * f x - x := by
  intro x
  have h := hSum (f x)
  rw [Function.leftInverse_invFun hBij.1 x] at h
  linarith

theorem continuous_second_difference_strictMono {f : ℝ → ℝ}
    (hCont : Continuous f) (hInj : Function.Injective f)
    (hStep : ∀ x, f (f x) = 2 * f x - x) : StrictMono f := by
  rcases hCont.strictMono_of_inj hInj with hm | ha
  · exact hm
  · have h01 := ha (show (0 : ℝ) < 1 by norm_num)
    have hff := ha h01
    rw [hStep 0, hStep 1] at hff
    linarith

theorem second_difference_natural_orbit {f : ℝ → ℝ}
    (hStep : ∀ x, f (f x) = 2 * f x - x) (n : ℕ) (x : ℝ) :
    f^[n] x = x + (n : ℝ) * (f x - x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, hStep, Nat.cast_succ]
    ring

theorem ordered_linear_orbits_slope_le {a b c d : ℝ}
    (h : ∀ n : ℕ, a + (n : ℝ) * b ≤ c + (n : ℝ) * d) : b ≤ d := by
  by_contra hn
  have hbd : 0 < b - d := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨n, hn⟩ := exists_nat_gt ((c - a) / (b - d))
  have hm := (div_lt_iff₀ hbd).mp hn
  have ho := h n
  nlinarith

theorem monotone_second_difference_displacement {f : ℝ → ℝ}
    (hMono : Monotone f) (hStep : ∀ x, f (f x) = 2 * f x - x)
    {x y : ℝ} (hxy : x ≤ y) : f x - x ≤ f y - y := by
  apply ordered_linear_orbits_slope_le (a := x) (c := y)
  intro n
  have h := hMono.iterate n hxy
  simpa only [second_difference_natural_orbit hStep] using h

theorem inverse_average_translation_classification {f : ℝ → ℝ}
    (hCont : Continuous f) (hBij : Function.Bijective f)
    (hSum : ∀ x, f x + Function.invFun f x = 2 * x) :
    ∀ x, f x = x + f 0 := by
  have hStep := inverse_average_second_difference hBij hSum
  have hMono := continuous_second_difference_strictMono hCont hBij.1 hStep
  have hRight := Function.rightInverse_invFun hBij.2
  have hInvMono : Monotone (Function.invFun f) := by
    intro x y hxy
    apply hMono.le_iff_le.mp
    simpa only [hRight x, hRight y] using hxy
  have hInvStep : ∀ x, Function.invFun f (Function.invFun f x) =
      2 * Function.invFun f x - x := by
    intro x
    have h := hSum (Function.invFun f x)
    rw [hRight x] at h
    linarith
  have hDisplacement {x y : ℝ} (hxy : x ≤ y) : f x - x = f y - y := by
    have hForward := monotone_second_difference_displacement hMono.monotone hStep hxy
    have hBackward := monotone_second_difference_displacement hInvMono hInvStep hxy
    have hx := hSum x
    have hy := hSum y
    linarith
  intro x
  rcases le_total x 0 with hx | hx
  · have h := hDisplacement hx
    linarith
  · have h := hDisplacement hx
    linarith

theorem inverse_average_fixed_point_identity {f : ℝ → ℝ}
    (hCont : Continuous f) (hBij : Function.Bijective f)
    (hFixed : ∃ u, f u = u)
    (hSum : ∀ x, f x + Function.invFun f x = 2 * x) : ∀ x, f x = x := by
  have h := inverse_average_translation_classification hCont hBij hSum
  obtain ⟨u, hu⟩ := hFixed
  have hZero : f 0 = 0 := by have := h u; linarith
  intro x
  simpa only [hZero, add_zero] using h x

theorem inverse_average_translation_iff (f : ℝ → ℝ) :
    (Continuous f ∧ Function.Bijective f ∧
      ∀ x, f x + Function.invFun f x = 2 * x) ↔
      ∃ c, ∀ x, f x = x + c := by
  constructor
  · rintro ⟨hCont, hBij, hSum⟩
    exact ⟨f 0, inverse_average_translation_classification hCont hBij hSum⟩
  · rintro ⟨c, hEq⟩
    have hBij : Function.Bijective f := by
      constructor
      · intro x y hxy
        rw [hEq, hEq] at hxy
        linarith
      · intro y
        refine ⟨y - c, ?_⟩
        rw [hEq]
        ring
    refine ⟨?_, hBij, ?_⟩
    · have he : f = fun x => x + c := funext hEq
      rw [he]
      exact continuous_id.add continuous_const
    · intro x
      have hInv := Function.rightInverse_invFun hBij.2 x
      rw [hEq] at hInv
      rw [hEq]
      linarith

theorem inverse_average_explicit_inverse {f : ℝ → ℝ}
    (hCont : Continuous f) (hBij : Function.Bijective f)
    (hSum : ∀ x, f x + Function.invFun f x = 2 * x) :
    ∀ x, Function.invFun f x = x - f 0 := by
  intro x
  have h := hSum x
  rw [inverse_average_translation_classification hCont hBij hSum x] at h
  linarith

theorem no_pointwise_reciprocal_average {f : ℝ → ℝ}
    (hSum : ∀ x, f x + (f x)⁻¹ = 2 * x) : False := by
  have h : f (1 / 2) + (f (1 / 2))⁻¹ = 1 := by
    convert hSum (1 / 2) using 1 <;> ring
  by_cases hz : f (1 / 2) = 0
  · simp only [hz, inv_zero, add_zero] at h
    exact zero_ne_one h
  · have hm := congrArg (fun z : ℝ => z * f (1 / 2)) h
    dsimp only at hm
    rw [add_mul, inv_mul_cancel₀ hz, one_mul] at hm
    nlinarith [sq_nonneg (f (1 / 2) - 1 / 2)]

theorem solution (h : ℝ → ℝ) (h_bij : Function.Bijective h)
    (h_cont : Continuous h) (h_fixed : ∃ u, h u = u)
    (h_sum : ∀ x, h x + h⁻¹ x = 2 * x) : ∀ x, h x = x := by
  exact False.elim (no_pointwise_reciprocal_average h_sum)

#print axioms inverse_average_second_difference
#print axioms continuous_second_difference_strictMono
#print axioms second_difference_natural_orbit
#print axioms ordered_linear_orbits_slope_le
#print axioms monotone_second_difference_displacement
#print axioms inverse_average_translation_classification
#print axioms inverse_average_fixed_point_identity
#print axioms inverse_average_translation_iff
#print axioms inverse_average_explicit_inverse
#print axioms no_pointwise_reciprocal_average
#print axioms solution
