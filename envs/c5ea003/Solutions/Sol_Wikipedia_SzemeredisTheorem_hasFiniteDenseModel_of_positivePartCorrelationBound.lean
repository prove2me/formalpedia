-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_of_positivePartCorrelationBound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:31.779875+00:00
-- url     : https://prove2.me/submissions/ad7db03b-f418-4253-adeb-74d748375adf

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_dual_apply_dualErrorVector
import Theorems.Thm_Wikipedia_SzemeredisTheorem_dual_apply_eq_sum_coefficient
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_finiteDenseModel_separator
import Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_finiteTestCombination

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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







theorem finitePairing_sub_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f - g) q =
      finitePairing f q - finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring











































@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl



theorem mem_profileErrorSet_iff
    {τ : Type*} {ε : ℝ} {e : τ → ℝ} :
    e ∈ profileErrorSet τ ε ↔ ∀ t, |e t| ≤ ε := by
  constructor
  · rintro ⟨hlower, hupper⟩ t
    exact abs_le.mpr ⟨hlower t, hupper t⟩
  · intro h
    exact
      ⟨fun t => (abs_le.mp (h t)).1,
        fun t => (abs_le.mp (h t)).2⟩















































/-- Applying a dual separator to a profile is the normalized pairing with
the corresponding linear combination of the original tests. -/
theorem dual_profile_eq_pairing_combination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ))
    (q : τ → Ω → ℝ) (f : Ω → ℝ) :
    L (finiteTestProfile q f) =
      finitePairing f
        (finiteTestCombination q (dualCoefficient L)) := by
  rw [dual_apply_eq_sum_coefficient,
    finitePairing_finiteTestCombination]
  apply Fintype.sum_congr
  intro t
  rw [finiteTestProfile_apply]



theorem dualErrorVector_mem
    {τ : Type*} [Fintype τ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (L : StrongDual ℝ (τ → ℝ)) :
    dualErrorVector ε L ∈ profileErrorSet τ ε := by
  rw [mem_profileErrorSet_iff]
  intro t
  rw [dualErrorVector, abs_mul, abs_of_nonneg hε]
  have hsign :
      |((SignType.sign (dualCoefficient L t) : SignType) : ℝ)| ≤ 1 := by
    rw [sign_apply]
    split_ifs <;> norm_num
  simpa using mul_le_mul_of_nonneg_left hsign hε











@[simp]
theorem positivePart_of_nonneg
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : 0 ≤ q x) :
    positivePart q x = q x :=
  max_eq_left hx

@[simp]
theorem positivePart_of_nonpos
    {Ω : Type*} {q : Ω → ℝ} {x : Ω}
    (hx : q x ≤ 0) :
    positivePart q x = 0 :=
  max_eq_right hx







theorem positiveSupportIndicator_unitBounded
    {Ω : Type*} (q : Ω → ℝ) :
    IsUnitBounded (positiveSupportIndicator q) := by
  constructor <;> intro x <;>
    simp only [positiveSupportIndicator] <;>
    split <;> norm_num

@[simp]
theorem positiveSupportIndicator_mul
    {Ω : Type*} (q : Ω → ℝ) (x : Ω) :
    positiveSupportIndicator q x * q x =
      positivePart q x := by
  by_cases hx : 0 ≤ q x
  · simp [positiveSupportIndicator, positivePart, hx]
  · have hx' : q x ≤ 0 := le_of_not_ge hx
    simp [positiveSupportIndicator, positivePart, hx, hx']

/-- Exact support function of the pointwise unit cube. -/
theorem finitePairing_positiveSupportIndicator
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (positiveSupportIndicator q) q =
      mean (positivePart q) := by
  apply congrArg mean
  funext x
  exact positiveSupportIndicator_mul q x



/-- Domination by a majorant turns an arbitrary separator into a
positive-part test of the majorant. -/
theorem finitePairing_le_majorant_positivePart
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x) :
    finitePairing f q ≤ finitePairing ν (positivePart q) := by
  apply mean_mono
  intro x
  by_cases hx : 0 ≤ q x
  · rw [positivePart_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right (hfν x) hx
  · rw [positivePart_of_nonpos (le_of_not_ge hx), mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos
      (hf0 x) (le_of_not_ge hx)

/-- The pairing of the constant-one function is the mean. -/
@[simp]
theorem finitePairing_one_left
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    finitePairing (fun _ : Ω => (1 : ℝ)) q = mean q := by
  simp [finitePairing]

/-- Core dual contradiction in the dense-model theorem.  If one separator
beats every function in the unit cube by a strict gap `δ`, then `ν - 1`
correlates with its positive part by more than `δ`. -/
theorem majorant_positivePart_correlation_of_separates_unitCube
    {Ω : Type*} [Fintype Ω]
    {f ν q : Ω → ℝ} {δ : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hsep :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g q + δ < finitePairing f q) :
    δ < finitePairing (ν - fun _ => 1) (positivePart q) := by
  have hsupport := hsep (positiveSupportIndicator q)
    (positiveSupportIndicator_unitBounded q)
  rw [finitePairing_positiveSupportIndicator] at hsupport
  have hmajorant :
      finitePairing f q ≤ finitePairing ν (positivePart q) :=
    finitePairing_le_majorant_positivePart
      (q := q) hf0 hfν
  rw [finitePairing_sub_left, finitePairing_one_left]
  linarith









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
/-- Finite dense-model theorem.  A majorized nonnegative function admits a
`[0,1]`-valued model against every test in a finite family whenever the
majorant obeys the homogeneous positive-part correlation bound. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {f ν : Ω → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo : HasPositivePartCorrelationBound q ν ε) :
    HasFiniteDenseModel q f ε := by
  by_contra hfail
  obtain ⟨L, _hL, hsep⟩ :=
    exists_finiteDenseModel_separator q f hε hfail
  have hsepPair :
      ∀ g : Ω → ℝ, IsUnitBounded g →
        finitePairing g
            (finiteTestCombination q (dualCoefficient L)) +
              ε * coefficientL1 (dualCoefficient L) <
          finitePairing f
            (finiteTestCombination q (dualCoefficient L)) := by
    intro g hg
    have h := hsep g hg (dualErrorVector ε L)
      (dualErrorVector_mem hε L)
    rw [map_add, dual_profile_eq_pairing_combination,
      dual_apply_dualErrorVector,
      dual_profile_eq_pairing_combination] at h
    exact h
  have hpositive :=
    majorant_positivePart_correlation_of_separates_unitCube
      hf0 hfν hsepPair
  exact (not_lt_of_ge (hpseudo (dualCoefficient L))) hpositive
