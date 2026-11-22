-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighFrozenDisplacement_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:59:07.538854+00:00
-- url     : https://prove2.me/submissions/b083a0c4-3b84-4a11-a688-69ddd3f14983

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/







/-! ## Fixed constants for the three row ledgers -/















/-! ## Quotient and logarithmic geometry -/

/-- A natural quotient differs from the corresponding real quotient by
strictly less than one. -/
theorem roughNatQuotient_sub_realQuotient_abs_lt_one
    {N r : ℕ} (hr : 0 < r) :
    |(((N / r : ℕ) : ℝ)) - (N : ℝ) / (r : ℝ)| < 1 := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hle :
      (((N / r : ℕ) : ℝ)) ≤ (N : ℝ) / (r : ℝ) :=
    Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  have hdecomp :=
    congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.div_add_mod N r)
  norm_num only [Nat.cast_add, Nat.cast_mul] at hdecomp
  have hmod : (((N % r : ℕ) : ℝ)) < (r : ℝ) := by
    exact_mod_cast Nat.mod_lt N hr
  calc
    (N : ℝ) / (r : ℝ) - ((N / r : ℕ) : ℝ) =
        ((N % r : ℕ) : ℝ) / (r : ℝ) := by
      field_simp [hrReal.ne']
      nlinarith
    _ < 1 := (div_lt_one hrReal).2 hmod

/-- The real quotient lies below the natural quotient plus one. -/
theorem roughRealQuotient_lt_natQuotient_add_one
    {N r : ℕ} (hr : 0 < r) :
    (N : ℝ) / (r : ℝ) < ((N / r : ℕ) : ℝ) + 1 := by
  have hfloor :=
    roughNatQuotient_sub_realQuotient_abs_lt_one
      (N := N) hr
  rw [abs_lt] at hfloor
  linarith

























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector -/
section


/-!
# Frozen-coordinate displacement on the deep exceptional core

This file isolates the displacement input used when the continuum mixture
kernel is frozen at

`log((2n)/b) / log(yNat n)`.

Natural quotient rounding contributes one unit at each lower endpoint.
On the deep prefix, the existing bound
`tangentPaperExceptionalCutoff <= n / L^2` absorbs that unit.  The upper and
high intervals then have displacement `O(1/L^2)`, while the broad interval
has displacement `O(1/L)`.

Only endpoint arithmetic and previously proved scale bounds occur here.
No interval count and no clipping-length estimate is asserted.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A normalized logarithmic displacement lemma -/

/-- If `t` is at least `s/R` and differs from `s` by at most `E`, then the
normalized logarithmic coordinates differ by at most
`R*E/(s*log y)`. -/
theorem abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
    {y : Nat} {s t R E : Real}
    (hlog : 0 < Real.log (y : Real))
    (hs : 0 < s) (hR : 1 <= R) (hE : 0 <= E)
    (htLower : s / R <= t)
    (hdistance : abs (t - s) <= E) :
    abs (Real.log t / Real.log (y : Real) -
        Real.log s / Real.log (y : Real)) <=
      R * E / (s * Real.log (y : Real)) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have htPos : 0 < t :=
    (div_pos hs hRpos).trans_le htLower
  have hlogAbs :
      abs (Real.log t - Real.log s) <= R * E / s := by
    by_cases hts : t <= s
    · have hlogTS : Real.log t <= Real.log s :=
        Real.log_le_log htPos hts
      have hgap : s - t <= E := by
        calc
          s - t <= abs (s - t) := le_abs_self _
          _ = abs (t - s) := abs_sub_comm _ _
          _ <= E := hdistance
      have hsRt : s <= t * R :=
        (div_le_iff₀ hRpos).mp htLower
      have hgapRatio :
          (s - t) / t <= R * E / s := by
        apply (div_le_div_iff₀ htPos hs).2
        calc
          (s - t) * s <= E * s :=
            mul_le_mul_of_nonneg_right hgap hs.le
          _ <= E * (t * R) :=
            mul_le_mul_of_nonneg_left hsRt hE
          _ = (R * E) * t := by ring
      rw [abs_of_nonpos (sub_nonpos.mpr hlogTS), neg_sub]
      calc
        Real.log s - Real.log t = Real.log (s / t) :=
          (Real.log_div hs.ne' htPos.ne').symm
        _ <= s / t - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hs htPos)
        _ = (s - t) / t := by
          field_simp [htPos.ne']
        _ <= R * E / s := hgapRatio
    · have hst : s <= t := le_of_not_ge hts
      have hlogST : Real.log s <= Real.log t :=
        Real.log_le_log hs hst
      have hgap : t - s <= E := by
        exact (le_abs_self (t - s)).trans hdistance
      have hscaleE : E <= R * E := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hR) hE]
      rw [abs_of_nonneg (sub_nonneg.mpr hlogST)]
      calc
        Real.log t - Real.log s = Real.log (t / s) :=
          (Real.log_div htPos.ne' hs.ne').symm
        _ <= t / s - 1 :=
          Real.log_le_sub_one_of_pos (div_pos htPos hs)
        _ = (t - s) / s := by
          field_simp [hs.ne']
        _ <= E / s :=
          div_le_div_of_nonneg_right hgap hs.le
        _ <= (R * E) / s :=
          div_le_div_of_nonneg_right hscaleE hs.le
  rw [← sub_div, abs_div, abs_of_pos hlog]
  calc
    abs (Real.log t - Real.log s) / Real.log (y : Real) <=
        (R * E / s) / Real.log (y : Real) :=
      div_le_div_of_nonneg_right hlogAbs hlog.le
    _ = R * E / (s * Real.log (y : Real)) := by ring

/-! ## Fixed rate constants -/













/-! ## Elementary deep-prefix scale reductions -/

private theorem deepCore_cast_le_self_div_two_L_sq
    {n b : Nat} {deltaStar : Real}
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2))
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2) :
    (b : Real) <= (n : Real) / (2 * L n ^ 2) := by
  have hbData := Finset.mem_Icc.mp hb
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      (2 : Real) * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  calc
    (b : Real) = (2 * (b : Real)) / 2 := by ring
    _ <= (tangentPaperExceptionalCutoff deltaStar n : Real) / 2 :=
      div_le_div_of_nonneg_right hbTwo (by norm_num)
    _ <= ((n : Real) / L n ^ 2) / 2 :=
      div_le_div_of_nonneg_right hcutoff (by norm_num)
    _ = (n : Real) / (2 * L n ^ 2) := by ring

private theorem deepCore_cast_le_self_div_two
    {n b : Nat} {deltaStar : Real}
    (hLone : 1 <= L n)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2))
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2) :
    (b : Real) <= (n : Real) / 2 := by
  have hbScale :=
    deepCore_cast_le_self_div_two_L_sq hb hcutoff
  have hLsq : 1 <= L n ^ 2 :=
    one_le_pow₀ (n := 2) hLone
  calc
    (b : Real) <= (n : Real) / (2 * L n ^ 2) := hbScale
    _ <= (n : Real) / 2 := by
      exact
        div_le_div_of_nonneg_left
          (Nat.cast_nonneg n) (by norm_num)
          (by nlinarith : (2 : Real) <= 2 * L n ^ 2)

private theorem short_displacement_scale
    {n : Nat} {H B a : Real}
    (hn : 0 < n) (ha : 0 <= a)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (_hH : 0 <= H)
    (hHupper : H <= 2 * a * (n : Real) / L n)
    (_hB : 0 <= B)
    (hBupper : B <= (n : Real) / (2 * L n ^ 2)) :
    ((H + B) / (n : Real)) *
        (1 / Real.log (yNat n : Real)) <=
      15 * (a + 1) / L n ^ 2 := by
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hHratio :
      H / (n : Real) <= 2 * a / L n := by
    calc
      H / (n : Real) <=
          (2 * a * (n : Real) / L n) / (n : Real) :=
        div_le_div_of_nonneg_right hHupper hnReal.le
      _ = 2 * a / L n := by
        field_simp [hnReal.ne', hL.ne']
  have hBratio :
      B / (n : Real) <= 1 / (2 * L n ^ 2) := by
    calc
      B / (n : Real) <=
          ((n : Real) / (2 * L n ^ 2)) / (n : Real) :=
        div_le_div_of_nonneg_right hBupper hnReal.le
      _ = 1 / (2 * L n ^ 2) := by
        field_simp [hnReal.ne', hL.ne']
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hproduct :
      (H / (n : Real) + B / (n : Real)) *
          (1 / Real.log (yNat n : Real)) <=
        (2 * a / L n + 1 / (2 * L n ^ 2)) *
          (5 / L n) := by
    exact
      mul_le_mul (add_le_add hHratio hBratio) hinvLog
        (one_div_nonneg.mpr hlog.le)
        (add_nonneg (div_nonneg (by positivity) hL.le)
          (div_nonneg (by norm_num)
            (mul_nonneg (by norm_num) (sq_nonneg (L n)))))
  have hLsqPos : 0 < L n ^ 2 := sq_pos_of_pos hL
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hround :
      5 / (2 * L n ^ 3) <= 5 / (2 * L n ^ 2) := by
    exact
      div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (by norm_num) hLsqPos)
        (mul_le_mul_of_nonneg_left hLsqLeCube (by norm_num))
  calc
    ((H + B) / (n : Real)) *
        (1 / Real.log (yNat n : Real)) =
        (H / (n : Real) + B / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by ring
    _ <= (2 * a / L n + 1 / (2 * L n ^ 2)) *
          (5 / L n) := hproduct
    _ = 10 * a / L n ^ 2 + 5 / (2 * L n ^ 3) := by ring
    _ <= 10 * a / L n ^ 2 + 5 / (2 * L n ^ 2) :=
      add_le_add le_rfl hround
    _ = (10 * a + 5 / 2) / L n ^ 2 := by ring
    _ <= 15 * (a + 1) / L n ^ 2 := by
      exact
        div_le_div_of_nonneg_right
          (by nlinarith : 10 * a + 5 / 2 <= 15 * (a + 1))
          hLsqPos.le

/-! ## Finite displacement bounds in adapter form -/



theorem
    roughCanonicalFourFiveDeepHighFrozenDisplacement_le
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n) (hc : 0 < c)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c /
          L n ^ 2 := by
  intro t ht
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hbScale :=
    deepCore_cast_le_self_div_two_L_sq hb hcutoff
  have hbHalf :=
    deepCore_cast_le_self_div_two hLone hb hcutoff
  have hsPos :
      0 < 2 * (n : Real) / (b : Real) :=
    div_pos (by positivity) hbPos
  have hsFour :
      4 <= 2 * (n : Real) / (b : Real) := by
    apply (le_div_iff₀ hbPos).2
    nlinarith
  have hdepthTwo :
      (K0 + 1) * upperTailLength c n <= 2 * n := by
    omega
  have hqLeLower :
      (2 * n - (K0 + 1) * upperTailLength c n) / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have htLowerQuotient :
      (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) <=
        t := by
    have hcast :
        (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) <=
          (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Real) := by
      exact_mod_cast hqLeLower
    exact hcast.trans ht.1
  have hqRound :
      ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) <
        (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) +
          1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := 2 * n - (K0 + 1) * upperTailLength c n) hbPosNat
  have hlowModel :
      ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) =
        2 * (n : Real) / (b : Real) -
          (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) := by
    rw [Nat.cast_sub hdepthTwo]
    push_cast
    ring
  have hlowerError :
      2 * (n : Real) / (b : Real) - t <
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    rw [hlowModel] at hqRound
    linarith
  have htUpperQuotient :
      t <= (((2 * n) / b : Nat) : Real) := by
    simpa only [roughCanonicalExceptionalPhysicalUpperEndpoint] using ht.2
  have htUpper :
      t <= 2 * (n : Real) / (b : Real) := by
    exact htUpperQuotient.trans
      (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (Nat.cast_div_le :
            (((2 * n) / b : Nat) : Real) <=
              ((2 * n : Nat) : Real) / (b : Real)))
  have hE :
      0 <=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    positivity
  have hdistance :
      abs (t - 2 * (n : Real) / (b : Real)) <=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hdepthReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        (n : Real) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          ((n / 2 : Nat) : Real) := by exact_mod_cast hdepth
      _ <= (n : Real) / 2 := Nat.cast_div_le (α := Real)
  have hsum :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) +
          (b : Real) <= (n : Real) := by
    linarith
  have hEHalf :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 <=
        (2 * (n : Real) / (b : Real)) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 =
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (b : Real) := by
        field_simp [hbPos.ne']
      _ <= (n : Real) / (b : Real) :=
        div_le_div_of_nonneg_right hsum hbPos.le
      _ = (2 * (n : Real) / (b : Real)) / 2 := by ring
  have hhalf :
      (2 * (n : Real) / (b : Real)) / 2 <= t := by
    linarith
  have hraw :=
    abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
      (y := yNat n) (s := 2 * (n : Real) / (b : Real))
      (t := t) (R := 2)
      (E :=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) + 1)
      hlog hsPos (by norm_num) hE hhalf hdistance
  have hrawEq :
      2 *
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) =
        (((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by
    field_simp [hbPos.ne', hnReal.ne', hlog.ne']
  have htailDepth :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        2 * (((K0 + 1 : Nat) : Real) * c) *
          (n : Real) / L n := by
    norm_num only [Nat.cast_mul]
    calc
      ((K0 + 1 : Nat) : Real) * (upperTailLength c n : Real) <=
          ((K0 + 1 : Nat) : Real) *
            (2 * c * (n : Real) / L n) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
      _ = 2 * (((K0 + 1 : Nat) : Real) * c) *
          (n : Real) / L n := by ring
  have hscale :=
    short_displacement_scale
      (n := n)
      (H := (((K0 + 1) * upperTailLength c n : Nat) : Real))
      (B := (b : Real)) (a := ((K0 + 1 : Nat) : Real) * c)
      hn (mul_nonneg (Nat.cast_nonneg _) hc.le)
      hLone hlogLower (Nat.cast_nonneg _) htailDepth
      (Nat.cast_nonneg _) hbScale
  calc
    abs (Real.log t / Real.log (yNat n : Real) -
        roughCanonicalFourFiveFrozenCoordinate n b) <=
        2 *
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) := by
      simpa only [roughCanonicalFourFiveFrozenCoordinate] using hraw
    _ =
        (((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := hrawEq
    _ <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c /
          L n ^ 2 := by
      exact hscale



/-! ## Simultaneous adapter-facing packaging -/











/-! ## Eventual simultaneous form -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {K0 n b : Nat} {c deltaStar : Real},
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Real) c →
      LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
        LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
            (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
          LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n))
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) ↑n)
                (Erdos390.Full.Scale.L n)) →
            LE.le.{0} (↑(Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n))
                (HDiv.hDiv.{0, 0, 0} (↑n) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) →
              LE.le.{0}
                  (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n))
                  (HDiv.hDiv.{0, 0, 0} n (2 : Nat)) →
                Membership.mem.{0, 0}
                    (Finset.Icc.{0} (1 : Nat)
                      (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) (2 : Nat)))
                    b →
                  ∀ (t : Real),
                    Membership.mem.{0, 0}
                        (Set.Icc.{0}
                          ↑(Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalLowerEndpoint n
                              deltaStar b
                              (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n)
                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                  (Erdos390.WholePaper.upperTailLength c n))))
                          ↑(Erdos390.WholePaper.BankPaperRealization.roughCanonicalExceptionalPhysicalUpperEndpoint b
                              (HMul.hMul.{0, 0, 0} (2 : Nat) n)))
                        t →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))
                            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n b)))
                        (HDiv.hDiv.{0, 0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighDisplacementConstant
                            K0 c)
                          (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeepHighFrozenDisplacement_le
