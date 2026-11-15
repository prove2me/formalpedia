-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasPositivePartCorrelationBound_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.668088+00:00
-- url     : https://prove2.me/submissions/14f2aa9e-26e5-489c-9dce-cee0a82efaa9

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_coefficientL1_eq_zero_iff

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators















@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]



















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise













theorem finitePairing_smul_right
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing f (c • q) = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring









































































theorem coefficientL1_nonneg
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    0 ≤ coefficientL1 c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _



/-- Scaling law for the coefficient `ℓ¹`-norm. -/
theorem coefficientL1_smul
    {τ : Type*} [Fintype τ] (a : ℝ) (c : τ → ℝ) :
    coefficientL1 (a • c) = |a| * coefficientL1 c := by
  classical
  simp [coefficientL1, abs_mul, Finset.mul_sum]





@[simp]
theorem finiteTestCombination_zero
    {Ω τ : Type*} [Fintype τ] (q : τ → Ω → ℝ) :
    finiteTestCombination q 0 = 0 := by
  classical
  ext x
  simp [finiteTestCombination]

/-- Scaling coefficients scales the corresponding test combination. -/
theorem finiteTestCombination_smul_coeff
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (a : ℝ) (c : τ → ℝ) :
    finiteTestCombination q (a • c) =
      a • finiteTestCombination q c := by
  classical
  ext x
  simp [finiteTestCombination, Finset.mul_sum, mul_assoc]

























/-- Positive part commutes with multiplication by a nonnegative scalar. -/
theorem positivePart_smul_of_nonneg
    {Ω : Type*} {a : ℝ} (ha : 0 ≤ a) (q : Ω → ℝ) :
    positivePart (a • q) = a • positivePart q := by
  ext x
  simp only [positivePart, Pi.smul_apply, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ ha, mul_zero]

























end Wikipedia.SzemeredisTheorem

end
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/
open Wikipedia.SzemeredisTheorem
open scoped Pointwise

open Wikipedia.SzemeredisTheorem in
/-- It suffices to verify the positive-part correlation estimate for
coefficient vectors of `ℓ¹`-norm one. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ)
    (h :
      HasNormalizedPositivePartCorrelationBound q ν ε) :
    HasPositivePartCorrelationBound q ν ε := by
  intro c
  by_cases hc : coefficientL1 c = 0
  · have hc0 : c = 0 :=
      (coefficientL1_eq_zero_iff c).mp hc
    subst c
    rw [hc]
    simp [finitePairing, positivePart]
  · have hcpos : 0 < coefficientL1 c :=
      lt_of_le_of_ne (coefficientL1_nonneg c) (Ne.symm hc)
    let A := coefficientL1 c
    let c' : τ → ℝ := A⁻¹ • c
    have hApos : 0 < A := hcpos
    have hc'L1 : coefficientL1 c' = 1 := by
      change coefficientL1 (A⁻¹ • c) = 1
      rw [coefficientL1_smul, abs_of_pos (inv_pos.mpr hApos)]
      exact inv_mul_cancel₀ hApos.ne'
    have hnormalized := h c' hc'L1
    have hcombination :
        finiteTestCombination q c' =
          A⁻¹ • finiteTestCombination q c := by
      exact finiteTestCombination_smul_coeff q A⁻¹ c
    rw [hcombination,
      positivePart_smul_of_nonneg (inv_nonneg.mpr hApos.le),
      finitePairing_smul_right] at hnormalized
    have hmul :=
      mul_le_mul_of_nonneg_left hnormalized hApos.le
    rw [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] at hmul
    simpa [A, mul_comm] using hmul
