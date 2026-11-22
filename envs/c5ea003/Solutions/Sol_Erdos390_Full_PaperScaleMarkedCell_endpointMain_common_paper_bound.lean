-- Prove2me | solution 1 for Erdos390.Full.PaperScaleMarkedCell.endpointMain_common_paper_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:25:16.669988+00:00
-- url     : https://prove2.me/submissions/b0fa7b23-86b5-4ad4-a41a-1dc83a6bc598

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.Full.PaperScaleEndpoint -/
section


/-! Quantitative endpoint specialization at the paper scale. -/

namespace Erdos390.Full.PaperScaleMarkedCell

private theorem abs_cast_natDiv_sub_realDiv_lt_one
    (x q : ℕ) (hq : 0 < q) :
    |((x / q : ℕ) : ℝ) - (x : ℝ) / (q : ℝ)| < 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hle : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) := Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  have hdecomp := congrArg (fun z : ℕ => (z : ℝ)) (Nat.div_add_mod x q)
  norm_num only [Nat.cast_add, Nat.cast_mul] at hdecomp
  have hmod : ((x % q : ℕ) : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.mod_lt x hq
  calc
    (x : ℝ) / (q : ℝ) - ((x / q : ℕ) : ℝ) =
        ((x % q : ℕ) : ℝ) / (q : ℝ) := by
      field_simp [hqR.ne']
      nlinarith
    _ < 1 := (div_lt_one hqR).2 hmod

private theorem abs_physicalBound_div_sub_lt_two
    (C : ℝ) (n q : ℕ) (hC : 0 ≤ C) (hq : 0 < q) :
    |((ArithmeticModel.physicalBound C n / q : ℕ) : ℝ) -
        C * (n : ℝ) / (q : ℝ)| < 2 := by
  let x := ArithmeticModel.physicalBound C n
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hxle : (x : ℝ) ≤ C * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hC (Nat.cast_nonneg n))
  have hxlt : C * (n : ℝ) < (x : ℝ) + 1 := Nat.lt_floor_add_one _
  have habsx : |(x : ℝ) - C * (n : ℝ)| < 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxle)]
    linarith
  have hdivFloor :
      |((x : ℝ) / (q : ℝ)) - C * (n : ℝ) / (q : ℝ)| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hqR]
    apply (div_lt_one hqR).2
    exact habsx.trans_le (by exact_mod_cast hq)
  calc
    |((x / q : ℕ) : ℝ) - C * (n : ℝ) / (q : ℝ)| ≤
        |((x / q : ℕ) : ℝ) - (x : ℝ) / (q : ℝ)| +
          |(x : ℝ) / (q : ℝ) - C * (n : ℝ) / (q : ℝ)| :=
      abs_sub_le _ _ _
    _ < 1 + 1 := add_lt_add
      (abs_cast_natDiv_sub_realDiv_lt_one x q hq) hdivFloor
    _ = 2 := by norm_num

private theorem abs_log_sub_log_le_log_two {X r : ℝ}
    (hr : 4 ≤ r) (hXr : |X - r| < 2) :
    |Real.log X - Real.log r| ≤ Real.log 2 := by
  have hdiff := abs_lt.mp hXr
  have hrpos : 0 < r := by linarith
  have hXlower : r / 2 ≤ X := by linarith
  have hXupper : X ≤ 2 * r := by linarith
  have hXpos : 0 < X := (div_pos hrpos (by norm_num)).trans_le hXlower
  have hlogLower : Real.log (r / 2) ≤ Real.log X :=
    Real.log_le_log (div_pos hrpos (by norm_num)) hXlower
  have hlogUpper : Real.log X ≤ Real.log (2 * r) :=
    Real.log_le_log hXpos hXupper
  apply abs_le.mpr
  constructor
  · have hlogDiv : Real.log (r / 2) = Real.log r - Real.log 2 := by
      rw [Real.log_div hrpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hlogDiv] at hlogLower
    linarith
  · have hlogMul : Real.log (2 * r) = Real.log 2 + Real.log r := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hrpos.ne']
    rw [hlogMul] at hlogUpper
    linarith

private theorem endpoint_coordinate_common_nat_bound
    (C : ℝ) (n g d y : ℕ) (hC : 0 < C) (hn : 0 < n)
    (hg : 0 < g) (hd : 0 < d) (hy : 1 < y)
    (hr : 4 ≤ C * (n : ℝ) / ((g * d : ℕ) : ℝ)) :
    |FriableAsymptotic.dickmanU
          (ArithmeticModel.physicalBound C n / (g * d)) y -
        (Scale.L n - Real.log (d : ℝ)) / Real.log (y : ℝ)| ≤
      (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) /
        Real.log (y : ℝ) := by
  let X : ℝ :=
    ((ArithmeticModel.physicalBound C n / (g * d) : ℕ) : ℝ)
  let r : ℝ := C * (n : ℝ) / ((g * d : ℕ) : ℝ)
  have hgd : 0 < g * d := mul_pos hg hd
  have hround : |X - r| < 2 := by
    simpa only [X, r] using
      abs_physicalBound_div_sub_lt_two C n (g * d) hC.le hgd
  have hlogClose : |Real.log X - Real.log r| ≤ Real.log 2 :=
    abs_log_sub_log_le_log_two hr hround
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hlogr :
      Real.log r = Real.log C + Scale.L n - Real.log (g : ℝ) -
        Real.log (d : ℝ) := by
    dsimp only [r, Scale.L]
    rw [Real.log_div (mul_ne_zero hC.ne' hnR.ne')
      (by positivity : (((g * d : ℕ) : ℝ)) ≠ 0),
      Real.log_mul hC.ne' hnR.ne', Nat.cast_mul,
      Real.log_mul hgR.ne' hdR.ne']
    ring
  have hnum :
      |Real.log X - (Scale.L n - Real.log (d : ℝ))| ≤
        Real.log 2 + |Real.log C - Real.log (g : ℝ)| := by
    rw [show Real.log X - (Scale.L n - Real.log (d : ℝ)) =
        (Real.log X - Real.log r) +
          (Real.log C - Real.log (g : ℝ)) by rw [hlogr]; ring]
    exact (abs_add_le _ _).trans (add_le_add hlogClose le_rfl)
  simp only [FriableAsymptotic.dickmanU]
  change |Real.log X / Real.log (y : ℝ) -
      (Scale.L n - Real.log (d : ℝ)) / Real.log (y : ℝ)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hylog]
  exact div_le_div_of_nonneg_right hnum hylog.le

theorem log_y_sub_log_yNat_bounds {n : ℕ} (hn : 0 < n)
    (hy2 : 2 ≤ ArithmeticModel.y n) :
    0 ≤ Real.log (ArithmeticModel.y n) -
          Real.log (ArithmeticModel.yNat n : ℝ) ∧
      Real.log (ArithmeticModel.y n) -
          Real.log (ArithmeticModel.yNat n : ℝ) ≤ Real.log 2 := by
  have hypos : 0 < ArithmeticModel.y n := Scale.y_pos hn
  have hyNatUpper : (ArithmeticModel.yNat n : ℝ) ≤ ArithmeticModel.y n :=
    Nat.floor_le hypos.le
  have hyNatLower : ArithmeticModel.y n / 2 ≤
      (ArithmeticModel.yNat n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (ArithmeticModel.y n)
    change ArithmeticModel.y n <
      (ArithmeticModel.yNat n : ℝ) + 1 at hfloor
    linarith
  have hyNatPos : (0 : ℝ) < (ArithmeticModel.yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogUpper : Real.log (ArithmeticModel.yNat n : ℝ) ≤
      Real.log (ArithmeticModel.y n) :=
    Real.log_le_log hyNatPos hyNatUpper
  have hlogLower : Real.log (ArithmeticModel.y n / 2) ≤
      Real.log (ArithmeticModel.yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (ArithmeticModel.y n / 2) =
      Real.log (ArithmeticModel.y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hlogDiv] at hlogLower
  constructor <;> linarith



private theorem common_nat_coordinate_sub_paper_bound
    {n d : ℕ} (hn : 1 < n) (hd : 0 < d)
    (hd4 : d ≤ ArithmeticModel.yNat n ^ 4)
    (hy2 : 2 ≤ ArithmeticModel.y n)
    (hlogLower : (1 / 5 : ℝ) * Scale.L n ≤
      Real.log (ArithmeticModel.yNat n : ℝ)) :
    |(Scale.L n - Real.log (d : ℝ)) /
          Real.log (ArithmeticModel.yNat n : ℝ) -
        paperDivisorCoordinate n d| ≤
      ((45 / 2 : ℝ) * Real.log 2) / Scale.L n := by
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  have ht : Real.log (ArithmeticModel.y n) =
      (2 / 9 : ℝ) * Scale.L n := Scale.log_y hnpos
  have htpos : 0 < Real.log (ArithmeticModel.y n) := by
    rw [ht]
    positivity
  have hyGap := log_y_sub_log_yNat_bounds hnpos hy2
  have hspos : 0 < Real.log (ArithmeticModel.yNat n : ℝ) := by
    have : 0 < (1 / 5 : ℝ) * Scale.L n := by positivity
    exact this.trans_le hlogLower
  have hyNatUpper : (ArithmeticModel.yNat n : ℝ) ≤ ArithmeticModel.y n :=
    Nat.floor_le (Scale.y_pos hnpos).le
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdCast : (d : ℝ) ≤ (ArithmeticModel.yNat n : ℝ) ^ 4 := by
    exact_mod_cast hd4
  have hlogd : Real.log (d : ℝ) ≤
      4 * Real.log (ArithmeticModel.yNat n : ℝ) := by
    have hlog := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at hlog
    norm_num at hlog
    exact hlog
  have hsle : Real.log (ArithmeticModel.yNat n : ℝ) ≤
      Real.log (ArithmeticModel.y n) :=
    Real.log_le_log
      (zero_lt_one.trans
        ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hspos))
      hyNatUpper
  have hA0 : 0 ≤ Scale.L n - Real.log (d : ℝ) := by
    rw [ht] at htpos
    have : Real.log (d : ℝ) ≤ (8 / 9 : ℝ) * Scale.L n := by
      calc
        Real.log (d : ℝ) ≤ 4 * Real.log (ArithmeticModel.yNat n : ℝ) := hlogd
        _ ≤ 4 * Real.log (ArithmeticModel.y n) := by linarith
        _ = (8 / 9 : ℝ) * Scale.L n := by rw [ht]; ring
    linarith
  have hAle : Scale.L n - Real.log (d : ℝ) ≤ Scale.L n := by
    have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hd)
    linarith
  have hpaper :
      paperDivisorCoordinate n d =
        (Scale.L n - Real.log (d : ℝ)) /
          Real.log (ArithmeticModel.y n) := by
    unfold paperDivisorCoordinate DickmanBasic.U
    rw [ht]
    field_simp [hL.ne']
  rw [hpaper]
  have hidentity :
      (Scale.L n - Real.log (d : ℝ)) /
            Real.log (ArithmeticModel.yNat n : ℝ) -
          (Scale.L n - Real.log (d : ℝ)) /
            Real.log (ArithmeticModel.y n) =
        (Scale.L n - Real.log (d : ℝ)) *
          (Real.log (ArithmeticModel.y n) -
            Real.log (ArithmeticModel.yNat n : ℝ)) /
          (Real.log (ArithmeticModel.yNat n : ℝ) *
            Real.log (ArithmeticModel.y n)) := by
    field_simp [hspos.ne', htpos.ne']
  rw [hidentity, abs_div, abs_mul,
    abs_of_nonneg hA0, abs_of_nonneg hyGap.1,
    abs_of_pos (mul_pos hspos htpos)]
  have hnum :
      (Scale.L n - Real.log (d : ℝ)) *
          (Real.log (ArithmeticModel.y n) -
            Real.log (ArithmeticModel.yNat n : ℝ)) ≤
        Scale.L n * Real.log 2 :=
    mul_le_mul hAle hyGap.2 hyGap.1 (hL.le)
  have hden :
      (2 / 45 : ℝ) * Scale.L n ^ 2 ≤
        Real.log (ArithmeticModel.yNat n : ℝ) *
          Real.log (ArithmeticModel.y n) := by
    rw [ht]
    nlinarith
  apply (div_le_div_iff₀ (mul_pos hspos htpos)
      (by positivity : 0 < Scale.L n)).2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    (Scale.L n - Real.log (d : ℝ)) *
          (Real.log (ArithmeticModel.y n) -
            Real.log (ArithmeticModel.yNat n : ℝ)) * Scale.L n ≤
        (Scale.L n * Real.log 2) * Scale.L n :=
      mul_le_mul_of_nonneg_right hnum hL.le
    _ ≤ ((45 / 2 : ℝ) * Real.log 2) *
        (Real.log (ArithmeticModel.yNat n : ℝ) *
          Real.log (ArithmeticModel.y n)) := by
      nlinarith

private theorem abs_rho_sub_rho_le_abs {a b : ℝ}
    (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |DickmanBasic.rho a - DickmanBasic.rho b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · have h := FriableAsymptotic.rho_lipschitz_of_le_five hab hb5
    rw [abs_sub_comm (DickmanBasic.rho a), abs_sub_comm a]
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hab)).symm
  · have hba : b ≤ a := le_of_not_ge hab
    have h := FriableAsymptotic.rho_lipschitz_of_le_five hba ha5
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hba)).symm

theorem endpointMain_common_paper_bound
    (C : ℝ) (n g d : ℕ) (hC : 0 < C) (hn : 1 < n)
    (hg : 0 < g) (hd : 0 < d)
    (hd4 : d ≤ ArithmeticModel.yNat n ^ 4)
    (hy2 : 2 ≤ ArithmeticModel.y n)
    (hlogLower : (1 / 5 : ℝ) * Scale.L n ≤
      Real.log (ArithmeticModel.yNat n : ℝ))
    (hr4 : 4 ≤ C * (n : ℝ) / ((g * d : ℕ) : ℝ))
    (hLr : Scale.L n ≤ C * (n : ℝ) / ((g * d : ℕ) : ℝ))
    (hlogX5 :
      Real.log ((ArithmeticModel.physicalBound C n / (g * d) : ℕ) : ℝ) ≤
        5 * Real.log (ArithmeticModel.yNat n : ℝ)) :
    |StructuredCellAsymptotic.endpointMain
          (ArithmeticModel.physicalBound C n / (g * d))
          (ArithmeticModel.yNat n) -
        (C * (n : ℝ) / ((g * d : ℕ) : ℝ)) *
          DickmanBasic.rho (paperDivisorCoordinate n d)| ≤
      (2 + 5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
          (45 / 2 : ℝ) * Real.log 2) *
        (C * (n : ℝ) / ((g * d : ℕ) : ℝ)) / Scale.L n := by
  let Xn : ℕ := ArithmeticModel.physicalBound C n / (g * d)
  let X : ℝ := (Xn : ℝ)
  let r : ℝ := C * (n : ℝ) / ((g * d : ℕ) : ℝ)
  let uX : ℝ := FriableAsymptotic.dickmanU Xn (ArithmeticModel.yNat n)
  let u0 : ℝ := (Scale.L n - Real.log (d : ℝ)) /
    Real.log (ArithmeticModel.yNat n : ℝ)
  let v : ℝ := paperDivisorCoordinate n d
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  have hgd : 0 < g * d := mul_pos hg hd
  have hround : |X - r| < 2 := by
    simpa only [X, Xn, r] using
      abs_physicalBound_div_sub_lt_two C n (g * d) hC.le hgd
  have hr4' : 4 ≤ r := by exact hr4
  have hXlower : r / 2 ≤ X := by
    have := abs_lt.mp hround
    linarith
  have hXtwo : 2 ≤ X := by
    exact (by linarith [hr4'] : 2 ≤ r / 2).trans hXlower
  have hyNatLog : 0 < Real.log (ArithmeticModel.yNat n : ℝ) := by
    have hpos : 0 < (1 / 5 : ℝ) * Scale.L n := by positivity
    exact hpos.trans_le hlogLower
  have huX0 : 0 ≤ uX := by
    dsimp only [uX, FriableAsymptotic.dickmanU, Xn, X]
    apply div_nonneg _ hyNatLog.le
    apply Real.log_nonneg
    change (1 : ℝ) ≤ X
    linarith [hXtwo]
  have huX5 : uX ≤ 5 := by
    dsimp only [uX, FriableAsymptotic.dickmanU, Xn]
    exact (div_le_iff₀ hyNatLog).2 (by simpa [mul_comm] using hlogX5)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hv5 : v ≤ 5 := by
    dsimp only [v, paperDivisorCoordinate]
    have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hd)
    have hylog : 0 < Real.log (ArithmeticModel.y n) := by
      rw [Scale.log_y hnpos]
      positivity
    unfold DickmanBasic.U
    have : 0 ≤ Real.log (d : ℝ) / Real.log (ArithmeticModel.y n) :=
      div_nonneg hlogd0 hylog.le
    linarith
  have hrhoX : |DickmanBasic.rho uX| ≤ 1 := by
    have hpos := DickmanBasic.rho_pos_on_zero_five huX0 huX5
    rw [abs_of_pos hpos]
    exact FriableAsymptotic.rho_le_one_of_le_five huX5
  have hyNatOne : 1 < ArithmeticModel.yNat n := by
    have : (1 : ℝ) < (ArithmeticModel.yNat n : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hyNatLog
    exact_mod_cast this
  have huXu0 := endpoint_coordinate_common_nat_bound C n g d
    (ArithmeticModel.yNat n) hC hnpos hg hd
    hyNatOne (by simpa only [r] using hr4')
  have hu0v := common_nat_coordinate_sub_paper_bound hn hd hd4 hy2 hlogLower
  have hinvLog : 1 / Real.log (ArithmeticModel.yNat n : ℝ) ≤
      5 / Scale.L n := by
    apply (div_le_div_iff₀ hyNatLog hL).2
    simpa only [one_mul] using (show Scale.L n ≤
      5 * Real.log (ArithmeticModel.yNat n : ℝ) by linarith)
  have huXu0' :
      |uX - u0| ≤
        (5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|)) /
          Scale.L n := by
    have hcoef : 0 ≤ Real.log 2 + |Real.log C - Real.log (g : ℝ)| :=
      add_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg _)
    calc
      |uX - u0| ≤
          (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) /
            Real.log (ArithmeticModel.yNat n : ℝ) := by
        simpa only [uX, u0] using huXu0
      _ = (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) *
          (1 / Real.log (ArithmeticModel.yNat n : ℝ)) := by ring
      _ ≤ (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) *
          (5 / Scale.L n) :=
        mul_le_mul_of_nonneg_left hinvLog hcoef
      _ = _ := by ring
  have huXv :
      |uX - v| ≤
        (5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
          (45 / 2 : ℝ) * Real.log 2) / Scale.L n := by
    calc
      |uX - v| ≤ |uX - u0| + |u0 - v| := abs_sub_le _ _ _
      _ ≤ (5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|)) /
            Scale.L n +
          ((45 / 2 : ℝ) * Real.log 2) / Scale.L n :=
        add_le_add huXu0' (by simpa only [u0, v] using hu0v)
      _ = _ := by ring
  have hrhoDiff :
      |DickmanBasic.rho uX - DickmanBasic.rho v| ≤
        (5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
          (45 / 2 : ℝ) * Real.log 2) / Scale.L n :=
    (abs_rho_sub_rho_le_abs huX5 hv5).trans huXv
  have hr0 : 0 ≤ r := by positivity
  have hroundScaled : |X - r| ≤ 2 * r / Scale.L n := by
    have htwo : (2 : ℝ) ≤ 2 * r / Scale.L n := by
      apply (le_div_iff₀ hL).2
      dsimp only [r] at hLr ⊢
      nlinarith
    exact hround.le.trans htwo
  unfold StructuredCellAsymptotic.endpointMain
  change |X * DickmanBasic.rho uX - r * DickmanBasic.rho v| ≤ _
  rw [show X * DickmanBasic.rho uX - r * DickmanBasic.rho v =
      (X - r) * DickmanBasic.rho uX +
        r * (DickmanBasic.rho uX - DickmanBasic.rho v) by ring]
  calc
    |(X - r) * DickmanBasic.rho uX +
        r * (DickmanBasic.rho uX - DickmanBasic.rho v)| ≤
      |(X - r) * DickmanBasic.rho uX| +
        |r * (DickmanBasic.rho uX - DickmanBasic.rho v)| :=
      abs_add_le _ _
    _ =
      |X - r| * |DickmanBasic.rho uX| +
        r * |DickmanBasic.rho uX - DickmanBasic.rho v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0]
    _ ≤ (2 * r / Scale.L n) * 1 +
        r * ((5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
          (45 / 2 : ℝ) * Real.log 2) / Scale.L n) :=
      add_le_add
        (mul_le_mul hroundScaled hrhoX (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hrhoDiff hr0)
    _ = (2 + 5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
          (45 / 2 : ℝ) * Real.log 2) * r / Scale.L n := by ring







end Erdos390.Full.PaperScaleMarkedCell

end

theorem solution :
∀ (C : Real) (n g d : Nat),
  LT.lt.{0} (0 : Real) C →
    LT.lt.{0} (1 : Nat) n →
      LT.lt.{0} (0 : Nat) g →
        LT.lt.{0} (0 : Nat) d →
          LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
            LE.le.{0} (2 : Real) (Erdos390.Full.ArithmeticModel.y n) →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                  (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
                LE.le.{0} (4 : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)) →
                  LE.le.{0} (Erdos390.Full.Scale.L n)
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)) →
                    LE.le.{0}
                        (Real.log
                          ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound C n)
                              (HMul.hMul.{0, 0, 0} g d)))
                        (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n))) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.StructuredCellAsymptotic.endpointMain
                              (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound C n)
                                (HMul.hMul.{0, 0, 0} g d))
                              (Erdos390.Full.ArithmeticModel.yNat n))
                            (HMul.hMul.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d))
                              (Erdos390.Full.DickmanBasic.rho
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))))
                        (HDiv.hDiv.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (2 : Real)
                                (HMul.hMul.{0, 0, 0} (5 : Real)
                                  (HAdd.hAdd.{0, 0, 0} (Real.log (2 : Real))
                                    (abs.{0} (HSub.hSub.{0, 0, 0} (Real.log C) (Real.log ↑g))))))
                              (HMul.hMul.{0, 0, 0} (45 / 2 : Real) (Real.log (2 : Real))))
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C ↑n) ↑(HMul.hMul.{0, 0, 0} g d)))
                          (Erdos390.Full.Scale.L n)) := by
  exact @Erdos390.Full.PaperScaleMarkedCell.endpointMain_common_paper_bound
