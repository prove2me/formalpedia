-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_window_hit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:00:22.590211+00:00
-- url     : https://prove2.me/submissions/c3ef6c24-a7cc-4172-9e19-d94c433d80e5

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
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

   
                                                 

                                                                              
                                                    
                         
                                                                            
                                                                            
  

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- A four-term word in a reciprocal orbit satisfies this quartic equation. -/
theorem four_term_orbit_quartic {R : Type*} [CommRing R]
    (x y t d d₁ d₂ a b : R)
    (h₀ : y + d = a * x) (h₁ : d₁ = b * y) (h₂ : t + d₂ = 0)
    (hd₀ : d₁ = a * d) (hd₁ : d₂ = b * d₁) :
    (d * (d + y)) ^ 2 = -x ^ 2 * y * t := by
  have hxd : x * d₁ = d * (d + y) := by
    linear_combination x * hd₀ - d * h₀
  have hsq : d₁ ^ 2 = -y * t := by
    linear_combination d₁ * h₁ - y * hd₁ + y * h₂
  calc
    (d * (d + y)) ^ 2 = (x * d₁) ^ 2 := by rw [hxd]
    _ = x ^ 2 * d₁ ^ 2 := by ring
    _ = -x ^ 2 * y * t := by rw [hsq]; ring

/-- The compatibility equation is homogeneous of degree four. -/
theorem quartic_equation_remove_scale {F : Type*} [Field F]
    (s x y t d : F) (hs : s ≠ 0)
    (h : (d * (d + s * y)) ^ 2 = -(s * x) ^ 2 * (s * y) * (s * t)) :
    ((d / s) * (d / s + y)) ^ 2 = -x ^ 2 * y * t := by
  apply mul_left_cancel₀ (pow_ne_zero 4 hs)
  calc
    s ^ 4 * ((d / s) * (d / s + y)) ^ 2 = (d * (d + s * y)) ^ 2 := by
      field_simp [hs]
      <;> ring
    _ = -(s * x) ^ 2 * (s * y) * (s * t) := h
    _ = s ^ 4 * (-x ^ 2 * y * t) := by ring











/-- Clearing the binomial profile directly into a residue ring. -/
theorem integral_cubic_scaled_mod_eval (p : ℕ) (m c : ℤ) (n : ℕ) :
    (6 : ZMod p) * ((m * risingBinomial n + c : ℤ) : ZMod p) =
      (m : ZMod p) * (((n : ZMod p) + 1) ^ 3 - ((n : ZMod p) + 1)) +
        6 * (c : ZMod p) := by
  have hB := congrArg (fun z : ℤ ↦ (z : ZMod p)) (six_mul_risingBinomial n)
  push_cast at hB ⊢
  linear_combination (m : ZMod p) * hB
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m c : ℤ) (T n p : ℕ) [Fact p.Prime]
    (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p) (hm : (m : ZMod p) ≠ 0)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hcert : CubicQuarticNonresidue r) (hphase : (n : ZMod p) = r - 3) :
    ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ m * risingBinomial (n + j) + c := by
  classical
  by_contra h
  have hagree : ∀ j : ℕ, j < 4 → u (n + j) = m * risingBinomial (n + j) + c := by
    intro j hj
    by_contra hne
    exact h ⟨j, hj, hne⟩
  let U : ℕ → ZMod p := fun j ↦ 6 * (u j : ZMod p)
  let V : ℕ → ZMod p := fun j ↦ 6 * (v j : ZMod p)
  have hN : ∀ j, T ≤ j → U (j + 1) + V j = (a j : ZMod p) * U j := by
    intro j hj
    have hh := congrArg (fun z : ℤ ↦ (z : ZMod p)) (hnum j hj)
    push_cast at hh
    dsimp [U, V]
    linear_combination (6 : ZMod p) * hh
  have hD : ∀ j, T ≤ j → V (j + 1) = (a j : ZMod p) * V j := by
    intro j hj
    have hh := congrArg (fun z : ℤ ↦ (z : ZMod p)) (hden j hj)
    push_cast at hh
    dsimp [V]
    linear_combination (6 : ZMod p) * hh
  have hroot' : (m : ZMod p) * (r ^ 3 - r) + 6 * (c : ZMod p) = 0 := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using hroot
  have heval (j : ℕ) (hj : j < 4) :
      U (n + j) = (m : ZMod p) *
        (((n : ZMod p) + (j : ZMod p) + 1) ^ 3 -
          ((n : ZMod p) + (j : ZMod p) + 1)) + 6 * (c : ZMod p) := by
    dsimp [U]
    rw [hagree j hj, integral_cubic_scaled_mod_eval]
    push_cast <;> rfl
  have hU₀ : U n = (m : ZMod p) * cubicLeftTwo r := by
    have hh := heval 0 (by decide)
    simp only [Nat.add_zero, Nat.cast_zero, add_zero] at hh
    rw [hphase] at hh
    dsimp [cubicLeftTwo]
    linear_combination hh + hroot'
  have hU₁ : U (n + 1) = (m : ZMod p) * cubicLeftOne r := by
    have hh := heval 1 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_one] at hh
    dsimp [cubicLeftOne]
    linear_combination hh + hroot'
  have hU₂ : U (n + 2) = 0 := by
    have hh := heval 2 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linear_combination hh + hroot'
  have hU₃ : U (n + 3) = (m : ZMod p) * cubicRightOne r := by
    have hh := heval 3 (by decide)
    rw [hphase] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [cubicRightOne]
    linear_combination hh + hroot'
  have h₀ := hN n hn
  have h₁ : V (n + 1) = (a (n + 1) : ZMod p) * U (n + 1) := by
    have hh := hN (n + 1) (by omega)
    simpa only [show n + 1 + 1 = n + 2 by omega, hU₂, zero_add] using hh
  have h₂ : U (n + 3) + V (n + 2) = 0 := by
    have hh := hN (n + 2) (by omega)
    simpa only [show n + 2 + 1 = n + 3 by omega, hU₂, mul_zero] using hh
  have hd₀ := hD n hn
  have hd₁ : V (n + 2) = (a (n + 1) : ZMod p) * V (n + 1) := by
    simpa only [show n + 1 + 1 = n + 2 by omega] using hD (n + 1) (by omega)
  have hq := four_term_orbit_quartic (U n) (U (n + 1)) (U (n + 3))
    (V n) (V (n + 1)) (V (n + 2)) (a n : ZMod p) (a (n + 1) : ZMod p)
    h₀ h₁ h₂ hd₀ hd₁
  rw [hU₀, hU₁, hU₃] at hq
  exact hcert (V n / (m : ZMod p))
    (quartic_equation_remove_scale (m : ZMod p) (cubicLeftTwo r)
      (cubicLeftOne r) (cubicRightOne r) (V n) hm hq)
