-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_primitive_integral_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:33:41.460599+00:00
-- url     : https://prove2.me/submissions/c401dc94-134f-4f79-a1d9-6365759e94f2

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_clean_windows_of_not_lower_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_constant_gcd_natural_quotient_tail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_positive_integral_coefficients_of_four_agreements
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_step_adjacent_coprime
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_profile_gcd_stabilises
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# Constructed primitive cubic tails below quarter density

The stabilising divisor, the exact
natural quotient recurrence, the integral profile coefficients, and their
Bezout certificate are produced from the original orbit. The index is never
reset: division by a fixed gcd does not replace n by n-N in the polynomial.

This eliminates a normalisation supplier, but does NOT prove that the primitive
constant is a unit. Integral primitive profiles with other constants remain in
the universal-density problem.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- A primitive consecutive pair supplies an explicit Bezout certificate for
the two integer coefficients of its common binomial profile. -/
theorem cubic_coefficients_bezout_of_primitive_pair
    (u v : ℕ) (m c B B' : ℤ) (hcop : Nat.Coprime u v)
    (hu : (u : ℤ) = m * B + c) (hv : (v : ℤ) = m * B' + c) :
    ∃ x y : ℤ, m * x + c * y = 1 := by
  have hb := Nat.gcd_eq_gcd_ab u v
  rw [hcop.gcd_eq_one] at hb
  norm_num only [Nat.cast_one] at hb
  rw [hu, hv] at hb
  refine ⟨B * Nat.gcdA u v + B' * Nat.gcdB u v,
    Nat.gcdA u v + Nat.gcdB u v, ?_⟩
  linear_combination -hb

/-- Natural quotient casting with nonzero divisor; separate from totalised
natural division, which cannot be treated as field division without hdiv. -/
theorem rational_cast_exact_nat_quotient (C g : ℕ) (hdiv : g ∣ C) (hg : 0 < g) :
    ((C / g : ℕ) : ℚ) = (C : ℚ) / (g : ℚ) := by
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  apply (eq_div_iff hgQ).mpr
  have h := Nat.div_mul_cancel hdiv
  exact_mod_cast h
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : 0 < κ)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ (N g : ℕ) (m c : ℤ), 0 < g ∧ 0 < m ∧
      (m : ℚ) * (g : ℚ) = 6 * κ ∧ (c : ℚ) * (g : ℚ) = η ∧
      (∃ x y : ℤ, m * x + c * y = 1) ∧
      ∀ n, N ≤ n →
        Nat.gcd (C n) (D n) = g ∧
        0 < C n / g ∧ 0 < D n / g ∧
        Nat.Coprime (C n / g) (D n / g) ∧
        C (n + 1) / g + D n / g = a n * (C n / g) ∧
        D (n + 1) / g = a n * (D n / g) ∧
        ((C n : ℚ) = κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η ↔
          ((C n / g : ℕ) : ℤ) = m * risingBinomial n + c) := by
  obtain ⟨_B, N, _hbound, hN⟩ := rational_cubic_profile_gcd_stabilises
    a C D κ η (ne_of_gt hκ) hCpos hC hD hlow
  let g := Nat.gcd (C N) (D N)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left (D N) (hCpos N)
  have hG : ∀ n, N ≤ n → Nat.gcd (C n) (D n) = g := hN
  have hq := constant_gcd_natural_quotient_tail a C D N g hg hCpos hDpos hC hD hG
  have hgQpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hgQ : (g : ℚ) ≠ 0 := ne_of_gt hgQpos
  obtain ⟨n, hn, hclean⟩ := clean_windows_of_not_lower_density
    {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
    4 (by decide) hlow N
  have ha : ∀ j : ℕ, j < 4 →
      ((((C (n + j) / g : ℕ) : ℤ)) : ℚ) =
        (κ / (g : ℚ)) * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
          (((n + j : ℕ) : ℚ) + 2) + η / (g : ℚ) := by
    intro j hj
    have hc : (C (n + j) : ℚ) =
        κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
          (((n + j : ℕ) : ℚ) + 2) + η := not_ne_iff.mp (hclean j hj)
    rw [Int.cast_natCast, rational_cast_exact_nat_quotient _ g
      (hq (n + j) (by omega)).1 hg, hc]
    ring
  obtain ⟨m, c, hmpos, hm, hc, heval⟩ :=
    cubic_positive_integral_coefficients_of_four_agreements
      (fun k ↦ ((C k / g : ℕ) : ℤ)) (κ / (g : ℚ)) (η / (g : ℚ))
      (div_pos hκ hgQpos) n ha
  have hcoeff : ∀ j : ℕ, j < 4 →
      ((C (n + j) / g : ℕ) : ℤ) = m * risingBinomial (n + j) + c := by
    intro j hj
    have hh := (ha j hj).trans (heval (n + j))
    exact_mod_cast hh
  have hqn := hq n hn
  have hadj : Nat.Coprime (C n / g) (C (n + 1) / g) :=
    primitive_step_adjacent_coprime (a n) _ _ _ hqn.2.2.2.2.2.1 hqn.2.2.2.2.1
  have hzero : ((C n / g : ℕ) : ℤ) = m * risingBinomial n + c := by
    simpa only [Nat.add_zero] using hcoeff 0 (by decide)
  have hbez := cubic_coefficients_bezout_of_primitive_pair
    (C n / g) (C (n + 1) / g) m c (risingBinomial n) (risingBinomial (n + 1))
    hadj hzero (hcoeff 1 (by decide))
  have hmscale : (m : ℚ) * (g : ℚ) = 6 * κ := by rw [hm]; field_simp [hgQ] <;> ring
  have hcscale : (c : ℚ) * (g : ℚ) = η := by rw [hc]; field_simp [hgQ] <;> ring
  refine ⟨N, g, m, c, hg, hmpos, hmscale, hcscale, hbez, ?_⟩
  intro k hk
  obtain ⟨hdivC, _hdivD, hpC, hpD, hcop, hnum, hden⟩ := hq k hk
  refine ⟨hG k hk, hpC, hpD, hcop, hnum, hden, ?_⟩
  have hquot := rational_cast_exact_nat_quotient (C k) g hdivC hg
  have he := heval k
  constructor
  · intro hagree
    have hQ : (((C k / g : ℕ) : ℤ) : ℚ) =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
      rw [Int.cast_natCast, hquot, hagree, ← he]
      ring
    exact_mod_cast hQ
  · intro hagree
    have hQ : ((C k / g : ℕ) : ℚ) =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
      have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hagree
      simpa only [Int.cast_natCast] using hcast
    rw [hquot, ← he] at hQ
    calc
      (C k : ℚ) = ((κ / (g : ℚ)) * (k : ℚ) * ((k : ℚ) + 1) *
          ((k : ℚ) + 2) + η / (g : ℚ)) * (g : ℚ) := (div_eq_iff hgQ).mp hQ
      _ = κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η := by
        field_simp [hgQ] <;> ring
