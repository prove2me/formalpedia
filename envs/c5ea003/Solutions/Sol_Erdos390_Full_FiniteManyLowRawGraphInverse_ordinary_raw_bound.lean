-- Prove2me | solution 1 for Erdos390.Full.FiniteManyLowRawGraphInverse.ordinary_raw_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:03:03.532604+00:00
-- url     : https://prove2.me/submissions/e3fdb6e4-a3eb-495b-8428-53d13826b34b

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.FiniteManyLowRawGraphInverse -/
section


/-!
# Ordinary raw inverse with a finite low block

This is the finite maximum-principle mechanism needed when a relative mesh
contains arbitrarily many cells below a fixed structural cutoff.  The low
rows are controlled by a separate diagonal-dominance estimate.  On the high
block the common interior anchor controls oscillation.  Low-to-high forcing
and the low contribution to the gauge are retained explicitly and then
absorbed in the literal raw supremum norm.

No inverse, surjectivity statement, or spectral gap occurs among the
hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteManyLowRawGraphInverse

open FiniteGraphQuotientInverse

variable {Low High : Type*} [Fintype Low] [Fintype High]





lemma graphOperator_inr_eq_high_add_low
    (edge : Sum Low High → Sum Low High → ℝ)
    (q : Sum Low High → ℝ) (i : High) :
    graphOperator edge q (.inr i) =
      graphOperator (highEdge edge) (highPart q) i +
        ∑ l : Low, edge (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l)) := by
  unfold graphOperator highEdge highPart
  rw [Fintype.sum_sum_type]
  ac_rfl

/-- Multi-low ordinary-coordinate estimate.  `hLow` is the direct low-row
diagonal estimate, while `hCross` and `hGaugeLow` are the two exact finite
sums produced from the product-kernel bound.  The theorem performs every
remaining maximum-principle, gauge, and absorption step. -/
theorem ordinary_raw_bound
    [Nonempty High]
    (edge : Sum Low High → Sum Low High → ℝ)
    (anchor : High → ℝ) (omega alpha q : Sum Low High → ℝ)
    {kappa anchorMass amin amax cross incoming gaugeRatio
      Clow epsLow G : ℝ}
    (hG : 0 ≤ G)
    (hkappa : 0 < kappa)
    (hAnchorMass : ∑ j : High, anchor j = anchorMass)
    (hAnchorMassPos : 0 < anchorMass)
    (hPositiveDom : ∀ i j : High,
      kappa * anchor j ≤ highEdge edge i j)
    (hAlphaHighLower : ∀ i : High, amin ≤ alpha (.inr i))
    (hAmin : 0 < amin)
    (hAlphaHighUpper : ∀ i : High, alpha (.inr i) ≤ amax)
    (hAlphaHighNonneg : ∀ i : High, 0 ≤ alpha (.inr i))
    (hAmax : 0 ≤ amax)
    (hCross : 0 ≤ cross) (hIncoming : 0 ≤ incoming)
    (hClow : 0 ≤ Clow) (hEpsLow : 0 ≤ epsLow)
    (hOmegaHigh : ∀ i : High, 0 ≤ omega (.inr i))
    (hOmegaHighTotal : 0 < ∑ i : High, omega (.inr i))
    (hGauge : ∑ x : Sum Low High, omega x * q x = 0)
    (hOutput : ∀ x : Sum Low High,
      |alpha x * graphOperator edge q x| ≤ G)
    (hLow : ∀ l : Low,
      |alpha (.inl l) * q (.inl l)| ≤
        Clow * G + epsLow * ‖fun x ↦ alpha x * q x‖)
    (hCrossRows : ∀ i : High,
      |∑ l : Low, edge (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        cross * ‖fun x ↦ alpha x * q x‖ / amin +
          incoming * (Clow * G +
            epsLow * ‖fun x ↦ alpha x * q x‖))
    (hGaugeLow :
      |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
        gaugeRatio * (∑ i : High, omega (.inr i)) *
          (Clow * G + epsLow * ‖fun x ↦ alpha x * q x‖))
    (hAbsorb :
      max epsLow
        (amax *
          (2 * (1 / (kappa * anchorMass)) *
              (cross / amin + incoming * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2) :
    ∀ x : Sum Low High,
      |alpha x * q x| ≤
        2 *
          max Clow
            (amax *
              (2 * (1 / (kappa * anchorMass)) *
                  (1 / amin + incoming * Clow) +
                gaugeRatio * Clow)) * G := by
  let B : ℝ := ‖fun x ↦ alpha x * q x‖
  let lowBudget : ℝ := Clow * G + epsLow * B
  let A : ℝ := 1 / (kappa * anchorMass)
  let Cmain : ℝ := max Clow
    (amax * (2 * A * (1 / amin + incoming * Clow) +
      gaugeRatio * Clow))
  let E : ℝ := max epsLow
    (amax * (2 * A * (cross / amin + incoming * epsLow) +
      gaugeRatio * epsLow))
  have hden : 0 < kappa * anchorMass := mul_pos hkappa hAnchorMassPos
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := norm_nonneg _
  have hlowBudget : 0 ≤ lowBudget := by
    dsimp only [lowBudget]
    positivity
  have hCmain : 0 ≤ Cmain := by
    exact hClow.trans (le_max_left _ _)
  have hE : 0 ≤ E := hEpsLow.trans (le_max_left _ _)
  have hfullGraph (i : High) :
      |graphOperator edge q (.inr i)| ≤ G / amin := by
    have hai : 0 < alpha (.inr i) := hAmin.trans_le (hAlphaHighLower i)
    have hscaled := hOutput (.inr i)
    have hfirst : |graphOperator edge q (.inr i)| ≤
        G / alpha (.inr i) := by
      apply (le_div_iff₀ hai).2
      rw [← abs_of_pos hai, ← abs_mul]
      simpa only [mul_comm] using hscaled
    exact hfirst.trans
      (div_le_div_of_nonneg_left hG hAmin (hAlphaHighLower i))
  have hhighGraph (i : High) :
      |graphOperator (highEdge edge) (highPart q) i| ≤
        G / amin + cross * B / amin + incoming * lowBudget := by
    have hidentity : graphOperator (highEdge edge) (highPart q) i =
        graphOperator edge q (.inr i) -
          ∑ l : Low, edge (.inr i) (.inl l) *
            (q (.inr i) - q (.inl l)) := by
      rw [graphOperator_inr_eq_high_add_low]
      ring
    have htri := abs_sub
      (graphOperator edge q (.inr i))
      (∑ l : Low, edge (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l)))
    have hcross := hCrossRows i
    change _ ≤ cross * B / amin + incoming * lowBudget at hcross
    calc
      |graphOperator (highEdge edge) (highPart q) i| =
          |graphOperator edge q (.inr i) -
            ∑ l : Low, edge (.inr i) (.inl l) *
              (q (.inr i) - q (.inl l))| := by
        rw [hidentity]
      _ ≤ |graphOperator edge q (.inr i)| +
          |∑ l : Low, edge (.inr i) (.inl l) *
            (q (.inr i) - q (.inl l))| := htri
      _ ≤ G / amin +
          (cross * B / amin + incoming * lowBudget) :=
        add_le_add (hfullGraph i) hcross
      _ = _ := by ring
  obtain ⟨mu, hosc⟩ := exists_center_of_graphOperator_bound
    (highEdge edge) anchor (highPart q) hPositiveDom hkappa
      (by simpa only [hAnchorMass] using hAnchorMassPos) hhighGraph
  let osc : ℝ := A *
    (G / amin + cross * B / amin + incoming * lowBudget)
  have hosc' (i : High) : |q (.inr i) - mu| ≤ osc := by
    have h := hosc i
    dsimp only [highPart] at h
    calc
      |q (.inr i) - mu| ≤
          (G / amin + cross * B / amin + incoming * lowBudget) /
            (kappa * ∑ j : High, anchor j) := h
      _ = osc := by
        rw [hAnchorMass]
        dsimp only [osc, A]
        field_simp [ne_of_gt hden]
  have hoscNonneg : 0 ≤ osc := by
    dsimp only [osc]
    positivity
  let Omega : ℝ := ∑ i : High, omega (.inr i)
  let lowSum : ℝ := ∑ l : Low, omega (.inl l) * q (.inl l)
  let highDiff : ℝ :=
    ∑ i : High, omega (.inr i) * (q (.inr i) - mu)
  have hOmega : 0 < Omega := by simpa only [Omega] using hOmegaHighTotal
  have hhighDiff : |highDiff| ≤ Omega * osc := by
    dsimp only [highDiff, Omega]
    calc
      |∑ i : High, omega (.inr i) * (q (.inr i) - mu)| ≤
          ∑ i : High, |omega (.inr i) * (q (.inr i) - mu)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : High, omega (.inr i) * osc := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hOmegaHigh i)]
        exact mul_le_mul_of_nonneg_left (hosc' i) (hOmegaHigh i)
      _ = (∑ i : High, omega (.inr i)) * osc := by
        rw [← Finset.sum_mul]
  have hmuIdentity : mu * Omega = -(lowSum + highDiff) := by
    have hg := hGauge
    rw [Fintype.sum_sum_type] at hg
    change lowSum + ∑ i : High, omega (.inr i) * q (.inr i) = 0 at hg
    have hsplit : (∑ i : High, omega (.inr i) * q (.inr i)) =
        highDiff + mu * Omega := by
      dsimp only [highDiff, Omega]
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsplit] at hg
    linarith
  have hmu : |mu| ≤ osc + gaugeRatio * lowBudget := by
    have hlow : |lowSum| ≤ gaugeRatio * Omega * lowBudget := by
      simpa only [lowSum, Omega, lowBudget, B] using hGaugeLow
    have hscaled : |mu| * Omega ≤
        Omega * (osc + gaugeRatio * lowBudget) := by
      calc
        |mu| * Omega = |mu * Omega| := by
          rw [abs_mul, abs_of_pos hOmega]
        _ = |lowSum + highDiff| := by rw [hmuIdentity, abs_neg]
        _ ≤ |lowSum| + |highDiff| := abs_add_le _ _
        _ ≤ gaugeRatio * Omega * lowBudget + Omega * osc :=
          add_le_add hlow hhighDiff
        _ = Omega * (osc + gaugeRatio * lowBudget) := by ring
    apply le_of_mul_le_mul_right _ hOmega
    simpa only [mul_comm] using hscaled
  have hhighRaw (i : High) :
      |alpha (.inr i) * q (.inr i)| ≤
        amax * (2 * osc + gaugeRatio * lowBudget) := by
    have hq : |q (.inr i)| ≤
        |q (.inr i) - mu| + |mu| := by
      have := abs_add_le (q (.inr i) - mu) mu
      simpa only [sub_add_cancel] using this
    rw [abs_mul, abs_of_nonneg (hAlphaHighNonneg i)]
    calc
      alpha (.inr i) * |q (.inr i)| ≤
          alpha (.inr i) * (|q (.inr i) - mu| + |mu|) :=
        mul_le_mul_of_nonneg_left hq (hAlphaHighNonneg i)
      _ ≤ amax * (osc + (osc + gaugeRatio * lowBudget)) := by
        apply mul_le_mul (hAlphaHighUpper i)
        · exact add_le_add (hosc' i) hmu
        · positivity
        · exact hAmax
      _ = amax * (2 * osc + gaugeRatio * lowBudget) := by ring
  have hcoord : ∀ x : Sum Low High,
      |alpha x * q x| ≤ Cmain * G + E * B := by
    intro x
    cases x with
    | inl l =>
        have hl := hLow l
        change |alpha (.inl l) * q (.inl l)| ≤ lowBudget at hl
        calc
          |alpha (.inl l) * q (.inl l)| ≤ lowBudget := hl
          _ = Clow * G + epsLow * B := by rfl
          _ ≤ Cmain * G + E * B :=
            add_le_add
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hG)
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
    | inr i =>
        have hh := hhighRaw i
        calc
          |alpha (.inr i) * q (.inr i)| ≤
              amax * (2 * osc + gaugeRatio * lowBudget) := hh
          _ =
              (amax * (2 * A * (1 / amin + incoming * Clow) +
                gaugeRatio * Clow)) * G +
              (amax * (2 * A * (cross / amin + incoming * epsLow) +
                gaugeRatio * epsLow)) * B := by
            dsimp only [osc, lowBudget]
            ring
          _ ≤ Cmain * G + E * B :=
            add_le_add
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hG)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
  have hBNorm : B ≤ Cmain * G + E * B := by
    change ‖fun x ↦ alpha x * q x‖ ≤ _
    rw [pi_norm_le_iff_of_nonneg (add_nonneg
      (mul_nonneg hCmain hG) (mul_nonneg hE hB))]
    intro x
    rw [Real.norm_eq_abs]
    exact hcoord x
  have hAbsorb' : E ≤ 1 / 2 := by
    simpa only [E, A] using hAbsorb
  have hEB : E * B ≤ (1 / 2) * B :=
    mul_le_mul_of_nonneg_right hAbsorb' hB
  intro x
  have hBfinal : B ≤ 2 * Cmain * G := by
    nlinarith
  exact (hcoord x).trans <| by
    calc
      Cmain * G + E * B ≤ Cmain * G + (1 / 2) * B :=
        add_le_add le_rfl hEB
      _ ≤ Cmain * G + (1 / 2) * (2 * Cmain * G) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hBfinal (by norm_num))
      _ = 2 * Cmain * G := by ring

end Erdos390.Full.FiniteManyLowRawGraphInverse

end

universe u_1 u_2
theorem solution :
∀ {Low : Type u_1} {High : Type u_2} [inst : Fintype.{u_1} Low] [inst_1 : Fintype.{u_2} High] [Nonempty.{u_2 + 1} High]
  (edge : Sum.{u_1, u_2} Low High → Sum.{u_1, u_2} Low High → Real) (anchor : High → Real)
  (omega alpha q : Sum.{u_1, u_2} Low High → Real)
  {kappa anchorMass amin amax cross incoming gaugeRatio Clow epsLow G : Real},
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (0 : Real) kappa →
      Eq.{1} (∑ j, anchor j) anchorMass →
        LT.lt.{0} (0 : Real) anchorMass →
          (∀ (i j : High),
              LE.le.{0} (HMul.hMul.{0, 0, 0} kappa (anchor j))
                (Erdos390.Full.FiniteManyLowRawGraphInverse.highEdge.{u_1, u_2} edge i j)) →
            (∀ (i : High), LE.le.{0} amin (alpha (Sum.inr.{u_1, u_2} i))) →
              LT.lt.{0} (0 : Real) amin →
                (∀ (i : High), LE.le.{0} (alpha (Sum.inr.{u_1, u_2} i)) amax) →
                  (∀ (i : High), LE.le.{0} (0 : Real) (alpha (Sum.inr.{u_1, u_2} i))) →
                    LE.le.{0} (0 : Real) amax →
                      LE.le.{0} (0 : Real) cross →
                        LE.le.{0} (0 : Real) incoming →
                          LE.le.{0} (0 : Real) Clow →
                            LE.le.{0} (0 : Real) epsLow →
                              (∀ (i : High), LE.le.{0} (0 : Real) (omega (Sum.inr.{u_1, u_2} i))) →
                                LT.lt.{0} (0 : Real) (∑ i, omega (Sum.inr.{u_1, u_2} i)) →
                                  Eq.{1} (∑ x, HMul.hMul.{0, 0, 0} (omega x) (q x)) (0 : Real) →
                                    (∀ (x : Sum.{u_1, u_2} Low High),
                                        LE.le.{0}
                                          (abs.{0}
                                            (HMul.hMul.{0, 0, 0} (alpha x)
                                              (Erdos390.Full.FiniteGraphQuotientInverse.graphOperator.{max u_1 u_2} edge
                                                q x)))
                                          G) →
                                      (∀ (l : Low),
                                          LE.le.{0}
                                            (abs.{0}
                                              (HMul.hMul.{0, 0, 0} (alpha (Sum.inl.{u_1, u_2} l))
                                                (q (Sum.inl.{u_1, u_2} l))))
                                            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                              (HMul.hMul.{0, 0, 0} epsLow
                                                (Norm.norm.{max u_1 u_2} fun x =>
                                                  HMul.hMul.{0, 0, 0} (alpha x) (q x))))) →
                                        (∀ (i : High),
                                            LE.le.{0}
                                              (abs.{0}
                                                (∑ l,
                                                  HMul.hMul.{0, 0, 0}
                                                    (edge (Sum.inr.{u_1, u_2} i) (Sum.inl.{u_1, u_2} l))
                                                    (HSub.hSub.{0, 0, 0} (q (Sum.inr.{u_1, u_2} i))
                                                      (q (Sum.inl.{u_1, u_2} l)))))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HDiv.hDiv.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} cross
                                                    (Norm.norm.{max u_1 u_2} fun x =>
                                                      HMul.hMul.{0, 0, 0} (alpha x) (q x)))
                                                  amin)
                                                (HMul.hMul.{0, 0, 0} incoming
                                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                                    (HMul.hMul.{0, 0, 0} epsLow
                                                      (Norm.norm.{max u_1 u_2} fun x =>
                                                        HMul.hMul.{0, 0, 0} (alpha x) (q x))))))) →
                                          LE.le.{0}
                                              (abs.{0}
                                                (∑ l,
                                                  HMul.hMul.{0, 0, 0} (omega (Sum.inl.{u_1, u_2} l))
                                                    (q (Sum.inl.{u_1, u_2} l))))
                                              (HMul.hMul.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0} gaugeRatio (∑ i, omega (Sum.inr.{u_1, u_2} i)))
                                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Clow G)
                                                  (HMul.hMul.{0, 0, 0} epsLow
                                                    (Norm.norm.{max u_1 u_2} fun x =>
                                                      HMul.hMul.{0, 0, 0} (alpha x) (q x))))) →
                                            LE.le.{0}
                                                (Max.max.{0} epsLow
                                                  (HMul.hMul.{0, 0, 0} amax
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                            (HMul.hMul.{0, 0, 0} kappa anchorMass)))
                                                        (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} cross amin)
                                                          (HMul.hMul.{0, 0, 0} incoming epsLow)))
                                                      (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                (1 / 2 : Real) →
                                              ∀ (x : Sum.{u_1, u_2} Low High),
                                                LE.le.{0} (abs.{0} (HMul.hMul.{0, 0, 0} (alpha x) (q x)))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} (2 : Real)
                                                      (Max.max.{0} Clow
                                                        (HMul.hMul.{0, 0, 0} amax
                                                          (HAdd.hAdd.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0}
                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HMul.hMul.{0, 0, 0} kappa anchorMass)))
                                                              (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                (HMul.hMul.{0, 0, 0} incoming Clow)))
                                                            (HMul.hMul.{0, 0, 0} gaugeRatio Clow)))))
                                                    G) := by
  exact @Erdos390.Full.FiniteManyLowRawGraphInverse.ordinary_raw_bound
