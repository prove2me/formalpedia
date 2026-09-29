-- Prove2me | solution 1 for ZetaLowerBnd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:14:08.195401+00:00
-- url     : https://prove2.me/submissions/f2b659b9-2996-4935-b97e-3391345a1028

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_ZetaLowerBound3
import Theorems.Thm_Zeta_diff_Bnd
import Theorems.Thm_logt_gt_one

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

theorem solution :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨C₁, C₁pos, hC₁⟩ := ZetaLowerBound3
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd

  -- Pick the right constants.
  -- Don't really like this because I can only do that after first finishing the proof.
  -- Is there a way to delay picking those
  let A := min A' ((C₁ / (4 * C₂)) ^ 4)
  have hA : A ∈ Ioc 0 (1 / 2) :=
    ⟨lt_min hA'.1 (by positivity), (min_le_left A' _).trans hA'.2⟩

  let C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  have hc_pos : 0 < C := by
    have:= A.rpow_le_rpow hA.1.le (min_le_right _ _) (inv_pos.mpr four_pos).le
    erw [Real.pow_rpow_inv_natCast (div_pos C₁pos (mul_pos four_pos C₂pos)).le four_ne_zero,
      le_div_iff₀ (mul_pos four_pos C₂pos)] at this
    norm_num [mul_assoc, C, mul_left_comm, C₂pos, hA.1,
      (mul_le_mul_of_nonneg_right this (A.rpow_nonneg hA.1.le _)).trans_lt', ←A.rpow_add]

  refine ⟨A, hA, C, hc_pos, fun σ t L ⟨σ_low_bound, σ_le_one⟩=>?_⟩

  -- From here I followed the proof found in the project's LaTeX outline
  let σ' := 1 + A / Real.log |t| ^  (9 : ℝ)

  have triangular :  ‖ζ (σ + t * I)‖ ≥  ‖ζ (σ' + t * I)‖ -  ‖ζ (σ + t * I) - ζ (σ' + t * I)‖ := by
    apply sub_le_iff_le_add.mpr.comp (sub_sub_self @_ (@_ : ℂ)▸norm_sub_le _ _).trans
      (by rw [add_comm])

  have one_leLogT : 1 ≤ Real.log |t| := (logt_gt_one L.le).le
  have one_half_le_log_pow : 1 / 2 ≤ Real.log |t| ^ 9 :=
    one_half_lt_one.le.trans <| one_le_pow₀ one_leLogT

  have σ'_ge : 1 ≤ σ' := by
    simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
      lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
      and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
      ofReal_div, ge_iff_le, le_add_iff_nonneg_right, A, C, σ']
    apply div_nonneg
    · apply le_min
      · linarith
      · have : (C₁ / (4 * C₂)) ^ 4 = ((C₁ / (4 * C₂)) ^ 2) ^ 2 := by ring
        rw [this]
        apply sq_nonneg
    · positivity

  have right_sub :  -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖ ≥ - C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    change - C₂ * Real.log |t| ^ 2 * (σ' - σ) ≤ -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖
    have := hC₂ σ σ' t L ?_ ?_ ?_
    · convert neg_le_neg this using 1
      · ring
      · congr! 1
        have : ζ (↑σ + ↑t * I) - ζ (↑σ' + ↑t * I) =
            - (ζ (↑σ' + ↑t * I) - ζ (↑σ + ↑t * I)) := by ring
        rw [this, norm_neg]
    · have : 1 - A' / Real.log |t| ≤ 1 - A / (Real.log |t|) ^ 9 := by
        gcongr
        · exact hA'.1.le
        · bound
        · bound
      linarith
    · have : σ' ≤ 1 + A := by
        simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
          lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
          and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
          ofReal_div, ge_iff_le, le_add_iff_nonneg_right, add_le_add_iff_left, le_inf_iff,
          σ', A, C]
        have : 1 ≤ Real.log t ^ (9 : ℕ) := by
          bound
        have : 1 ≤ Real.log t ^ (9 : ℝ) := by
          exact_mod_cast this
        refine ⟨?_, ?_⟩
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            left
            bound
          · exact le_trans (zero_le_one) this
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            right
            bound
          · exact le_trans (zero_le_one) this
      · bound [hA.2]
    · linarith

  have right' : -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖   ≥ - C₂ * 2 * A / Real.log |t| ^ 7 := by
    have := (abs t).log_pos (by bound)
    refine right_sub.trans' ((div_le_iff₀ (pow_pos this 7)).2 @?_|>.trans
      (mul_le_mul_of_nonpos_left (sub_le_sub_left σ_low_bound (1+_) )
        (by ·linear_combination C₂*this*(.log |t|))))
    exact (mod_cast (by linear_combination (2 *_* A) *div_self ↑(pow_pos this 09).ne'))

  have left_sub : ‖ζ (σ' + t * I)‖ ≥ C₁ * (σ' - 1) ^ ((3:ℝ) /4) / Real.log |t| ^ 4 := by
    use (hC₁ ⟨lt_add_of_pos_right (1) (by bound[hA.1]),
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))⟩ t L).trans' ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · simp_all only [gt_iff_lt, mem_Ioc, lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, pow_pos, and_self, inf_le_iff, true_or, sub_pos, mem_Ico,
        ofReal_add, ofReal_one, ofReal_div, ge_iff_le, le_add_iff_nonneg_right, neg_mul,
        neg_le_neg_iff, add_sub_cancel_left, σ', A, C]
      gcongr
      have :  Real.log |t| ^ ((1 : ℝ) / 4) ≤ Real.log |t| ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_leLogT (by norm_num)
      exact_mod_cast this

  have left' : ‖ζ (σ' + t * I)‖ ≥ C₁ * A ^ ((3:ℝ) /4) / Real.log |t| ^ 7 := by
    contrapose! hC₁
    use σ', ⟨lt_add_of_pos_right 1<|by bound[hA'.1],
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans ?_))⟩, t, L, hC₁.trans_le ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · norm_num only [σ', add_sub_cancel_left, A.div_rpow hA.1.le, mul_div, pow_pos, L.trans',
        ←Real.rpow_natCast, ←Real.rpow_mul, le_of_lt, Real.log_pos, refl, div_div, ←Real.rpow_sub]
      rw [Real.div_rpow hA.1.le, ← Real.rpow_mul (by linarith), ← mul_div_assoc, div_div, ← Real.rpow_add (by linarith)]
      · norm_num
      · apply Real.rpow_nonneg (by linarith)
  have ineq : ‖ζ (σ + t * I)‖ ≥ (C₁ * A ^ ((3:ℝ) /4) - C₂ * 2 * A) / Real.log |t| ^ 7 := by
    linear_combination left'+triangular+right'

  rw [mul_comm C₂] at ineq
  exact_mod_cast ineq

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

