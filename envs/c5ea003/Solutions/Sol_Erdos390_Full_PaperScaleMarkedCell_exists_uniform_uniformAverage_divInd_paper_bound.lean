-- Prove2me | solution 1 for Erdos390.Full.PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:20:25.632148+00:00
-- url     : https://prove2.me/submissions/f5d2a1c9-761c-4999-8470-bdae175af3cd

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.DivisibilityMomentBounds -/
section


/-!
# Exact multiple-counting moment bounds

The omitted-local-score step in Lemma 7.5 expands a valuation score into
divisor indicators and then counts common multiples.  This file proves that
finite combinatorial step for an arbitrary set of positive integers bounded
by one physical endpoint.  No smooth-number estimate or probability-model
assumption enters here.
-/

open scoped BigOperators

namespace Erdos390.Full.DivisibilityMomentBounds

open ArithmeticModel

noncomputable section



/-- A finite sum of an actual divisor indicator is the cardinality of the
corresponding filtered set. -/
theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]































end

end Erdos390.Full.DivisibilityMomentBounds

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos











/-- Four marks keep the paper coordinate inside the range on which the
constructed Dickman function is positive. -/
theorem paperDivisorCoordinate_mem_zero_five {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisorCoordinate n d ∧ paperDivisorCoordinate n d ≤ 5 := by
  have hnpos : 0 < n := by omega
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hyNatPos : 0 < yNat n := by
    by_contra hnot
    have hyNat0 : yNat n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hyNat0] at hd4
    omega
  have hyNatRpos : (0 : ℝ) < (yNat n : ℝ) := by exact_mod_cast hyNatPos
  have hdCast : (d : ℝ) ≤ (yNat n : ℝ) ^ 4 := by exact_mod_cast hd4
  have hlogdNat : Real.log (d : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogdY : Real.log (d : ℝ) ≤ 4 * Real.log (y n) := by
    calc
      Real.log (d : ℝ) ≤ 4 * Real.log (yNat n : ℝ) := hlogdNat
      _ ≤ 4 * Real.log (y n) := by linarith
  have hquot0 : 0 ≤ Real.log (d : ℝ) / Real.log (y n) :=
    div_nonneg hlogd0 hylog.le
  have hquot4 : Real.log (d : ℝ) / Real.log (y n) ≤ 4 :=
    (div_le_iff₀ hylog).2 (by simpa using hlogdY)
  unfold paperDivisorCoordinate DickmanBasic.U
  constructor <;> linarith

theorem paperDivisibilityMain_nonneg_le {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisibilityMain n d ∧
      paperDivisibilityMain n d ≤
        1 / (rho DickmanBasic.U * (d : ℝ)) := by
  have hv := paperDivisorCoordinate_mem_zero_five hn hd hd4
  have hrv : 0 < rho (paperDivisorCoordinate n d) :=
    rho_pos_on_zero_five hv.1 hv.2
  have hrv1 : rho (paperDivisorCoordinate n d) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hv.2
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold paperDivisibilityMain
  constructor
  · positivity
  · rw [div_div]
    exact div_le_div_of_nonneg_right hrv1 (mul_pos hrU hdR).le



















/-! ## Normalization algebra -/

/-- A quantitative ratio lemma which keeps the denominator lower bound
explicit.  It is used below with `y` equal to the actual unmarked cell
cardinality and `q` equal to its positive paper main term. -/
private theorem abs_normalized_ratio_sub_le
    {x y q t E F : ℝ} (hq : 0 < q) (hyhalf : q / 2 ≤ y)
    (hx : |x - q * t| ≤ E) (hy : |y - q| ≤ F) (ht : 0 ≤ t) :
    |x / y - t| ≤ 2 * (E + t * F) / q := by
  have hypos : 0 < y := (half_pos hq).trans_le hyhalf
  have hE : 0 ≤ E := (abs_nonneg (x - q * t)).trans hx
  have hF : 0 ≤ F := (abs_nonneg (y - q)).trans hy
  have hnum : 0 ≤ E + t * F := add_nonneg hE (mul_nonneg ht hF)
  have hinv : 1 / y ≤ 2 / q := by
    apply (div_le_div_iff₀ hypos hq).2
    linarith
  have hid : x / y - t = (x - q * t + t * (q - y)) / y := by
    field_simp [hypos.ne']
    ring
  rw [hid, abs_div, abs_of_pos hypos]
  calc
    |x - q * t + t * (q - y)| / y ≤
        (|x - q * t| + |t * (q - y)|) / y := by
      exact div_le_div_of_nonneg_right (abs_add_le _ _) hypos.le
    _ = (|x - q * t| + t * |y - q|) / y := by
      rw [abs_mul, abs_of_nonneg ht, abs_sub_comm q y]
    _ ≤ (E + t * F) / y := by
      apply div_le_div_of_nonneg_right _ hypos.le
      exact add_le_add hx (mul_le_mul_of_nonneg_left hy ht)
    _ = (E + t * F) * (1 / y) := by ring
    _ ≤ (E + t * F) * (2 / q) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ = 2 * (E + t * F) / q := by ring

/-- The actual uniform divisor probability is exactly the marked/unmarked
cardinality ratio. -/
theorem uniformAverage_divInd_eq_markedCell_ratio
    (P : Pattern) (lo hi y d : ℕ) :
    uniformAverage (structuredCell P lo hi y) (divInd d) =
      ((markedCell P lo hi y d).card : ℝ) /
        ((structuredCell P lo hi y).card : ℝ) := by
  unfold uniformAverage markedCell
  rw [sum_divInd_eq_card_filter]





/-- Paper-level normalized four-mark probability.  For every fixed physical
interval and head pattern, the actual uniform law on the finite structured
cell is eventually nonempty and its divisor probability has the common
Dickman translate, uniformly for all admissible `d ≤ yNat n ^ 4`. -/
theorem exists_uniform_uniformAverage_divInd_paper_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n d : ℕ},
      N₀ ≤ n → 0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      (structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).Nonempty ∧
      |uniformAverage
          (structuredCell P (physicalBound A n) (physicalBound B n)
            (yNat n))
          (divInd d) - paperDivisibilityMain n d| ≤
        K / ((d : ℝ) * L n) := by
  obtain ⟨K₀, hK₀, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  let K : ℝ := 2 * K₀ * (1 + 1 / rho DickmanBasic.U) / c
  have hK : 0 < K := by
    dsimp only [K]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hK₀)
        (add_pos_of_pos_of_nonneg zero_lt_one (one_div_nonneg.mpr hrU.le))) hc
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdenEvent : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ 2 * K₀ / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hLTop.eventually
        (Filter.eventually_ge_atTop (2 * K₀ / c))] with n hn hden
    exact ⟨hn, hden⟩
  obtain ⟨Nden, hNden⟩ := Filter.eventually_atTop.mp hdenEvent
  let N₀ := max Ncount Nden
  refine ⟨K, hK, N₀, ?_⟩
  intro n d hN hd hd4 hdsmooth hcop
  have hNcount : Ncount ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNden' : Nden ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hden⟩ := hNden n hNden'
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hL : 0 < L n := L_pos hn
  have hq : 0 < c * (n : ℝ) := mul_pos hc hnR
  have hscale : 2 * K₀ ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  let S : Finset ℕ :=
    structuredCell P (physicalBound A n) (physicalBound B n) (yNat n)
  have h1d4 : 1 ≤ yNat n ^ 4 := (show 1 ≤ d by omega).trans hd4
  have hbase₀ := hcount (n := n) (d := 1) hNcount (by omega)
    h1d4 (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |(S.card : ℝ) - c * (n : ℝ)| ≤ K₀ * (n : ℝ) / L n := by
    simpa [S, c, markedCell] using hbase₀
  have hKdiv : K₀ / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have hhalfError : K₀ * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K₀ * (n : ℝ) / L n = (K₀ / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hbaseHalf :
      |(S.card : ℝ) - c * (n : ℝ)| ≤ c * (n : ℝ) / 2 :=
    hbase.trans hhalfError
  have hScardHalf : c * (n : ℝ) / 2 ≤ (S.card : ℝ) := by
    have hlower := (abs_le.mp hbaseHalf).1
    linarith
  have hScardR : 0 < (S.card : ℝ) :=
    (half_pos hq).trans_le hScardHalf
  have hScard : 0 < S.card := by exact_mod_cast hScardR
  have hSnonempty : S.Nonempty := Finset.card_pos.mp hScard
  have hmarked₀ := hcount (n := n) (d := d) hNcount hd hd4
    hdsmooth hcop
  have hmarked :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) -
          (c * (n : ℝ)) * paperDivisibilityMain n d| ≤
        K₀ * (n : ℝ) / ((d : ℝ) * L n) := by
    rw [paperMarkedMain_eq_density_mul_divisibility P A B hd] at hmarked₀
    simpa [c, mul_assoc] using hmarked₀
  have ht := paperDivisibilityMain_nonneg_le hn hd hd4
  have hratio := abs_normalized_ratio_sub_le hq hScardHalf hmarked hbase ht.1
  have hFnonneg : 0 ≤ K₀ * (n : ℝ) / L n := by positivity
  have htF :
      paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        (1 / (rho DickmanBasic.U * (d : ℝ))) *
          (K₀ * (n : ℝ) / L n) :=
    mul_le_mul_of_nonneg_right ht.2 hFnonneg
  have hEF :
      K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        (K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n) := by
    calc
      K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          (1 / (rho DickmanBasic.U * (d : ℝ))) *
            (K₀ * (n : ℝ) / L n) := by linarith [htF]
      _ = (K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n) := by ring
  have hratio' :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) / (S.card : ℝ) -
          paperDivisibilityMain n d| ≤
        2 * ((K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n)) / (c * (n : ℝ)) := by
    exact hratio.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEF (by norm_num)) hq.le)
  have hfinal :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) / (S.card : ℝ) -
          paperDivisibilityMain n d| ≤ K / ((d : ℝ) * L n) := by
    calc
      _ ≤ 2 * ((K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n)) / (c * (n : ℝ)) := hratio'
      _ = K / ((d : ℝ) * L n) := by
        dsimp only [K]
        field_simp [hc.ne', hrU.ne', hnR.ne', hdR.ne', hL.ne']
  refine ⟨?_, ?_⟩
  · simpa only [S] using hSnonempty
  · rw [uniformAverage_divInd_eq_markedCell_ratio]
    simpa only [S] using hfinal

end

end Erdos390.Full.PaperScaleMarkedCell

end

theorem solution :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A B : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A B →
      ∃ K,
        And (LT.lt.{0} (0 : Real) K)
          (∃ N₀,
            ∀ {n d : Nat},
              LE.le.{0} N₀ n →
                LT.lt.{0} (0 : Nat) d →
                  LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                    Membership.mem.{0, 0}
                        (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat))) d →
                      Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                        And
                          (Finset.Nonempty.{0}
                            (Erdos390.Full.StructuredCells.structuredCell P
                              (Erdos390.Full.ArithmeticModel.physicalBound A n)
                              (Erdos390.Full.ArithmeticModel.physicalBound B n) (Erdos390.Full.ArithmeticModel.yNat n)))
                          (LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.DivisibilityMomentBounds.uniformAverage
                                  (Erdos390.Full.StructuredCells.structuredCell P
                                    (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                    (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                    (Erdos390.Full.ArithmeticModel.yNat n))
                                  (Erdos390.Full.ArithmeticModel.divInd d))
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n d)))
                            (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))))) := by
  exact @Erdos390.Full.PaperScaleMarkedCell.exists_uniform_uniformAverage_divInd_paper_bound
