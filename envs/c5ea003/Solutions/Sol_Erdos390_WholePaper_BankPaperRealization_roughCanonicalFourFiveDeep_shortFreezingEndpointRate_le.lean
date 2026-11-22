-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:00:14.992659+00:00
-- url     : https://prove2.me/submissions/e176b1fa-9fdd-4009-a25e-f8919aa09cf9

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector -/
section


/-!
# Deep exceptional four/five interval estimates

This connector assembles the three inputs already isolated for a deep
smooth core:

* the uniform arithmetic `Z / L^3` estimate;
* freezing at the literal coordinate, using the uniform compact `C¹`
  kernel bound and the deep displacement package;
* the literal endpoint-length errors.

The upper and high intervals use their eventual no-clipping conclusions.
The broad interval continues to use its clipped lower endpoint.  If that
clipping passes the broad upper endpoint, the literal interval is empty and
the same endpoint budget controls the removed frozen main term.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Algebraic rate absorption -/

/-- The two non-arithmetic terms produced by the freezing adapter for a
short deep interval are absorbed at the `Z/L^3+1` rate. -/
theorem roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
    {Z ell logY literal C D a : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) (hD : 0 <= D) (ha : 0 <= a)
    (hliteral : literal <= 2 * a * Z / ell + 1)
    (hliteralNonneg : 0 <= literal) :
    (((literal / logY) * C) * (D / ell ^ 2) +
        (C / logY) * 1) <=
      (5 * C * D * (2 * a + 1) + 5 * C) *
        (Z / ell ^ 3 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hfiveL : 0 <= 5 / ell := div_nonneg (by norm_num) hL.le
  have hscaledCD :
      0 <= C * (D / ell ^ 2) :=
    mul_nonneg hC (div_nonneg hD (sq_nonneg ell))
  have hLcubeLeFour : ell ^ 3 <= ell ^ 4 := by
    calc
      ell ^ 3 = ell ^ 3 * 1 := by ring
      _ <= ell ^ 3 * ell :=
        mul_le_mul_of_nonneg_left hLone (pow_nonneg hL.le 3)
      _ = ell ^ 4 := by ring
  have hZfour : Z / ell ^ 4 <= Z / ell ^ 3 :=
    div_le_div_of_nonneg_left hZ (pow_pos hL 3) hLcubeLeFour
  have hInvCube : 1 / ell ^ 3 <= 1 :=
    (div_le_one (pow_pos hL 3)).2
      (one_le_pow₀ (n := 3) hLone)
  have hq : 0 <= Z / ell ^ 3 :=
    div_nonneg hZ (pow_nonneg hL.le 3)
  have hqOne : 1 <= Z / ell ^ 3 + 1 := by linarith
  have hcoeffMain : 0 <= 10 * a * C * D := by positivity
  have hcoeffUnit : 0 <= 5 * C * D := by positivity
  have hfreeze :
      ((literal / logY) * C) * (D / ell ^ 2) <=
        (5 * C * D * (2 * a + 1)) *
          (Z / ell ^ 3 + 1) := by
    calc
      ((literal / logY) * C) * (D / ell ^ 2) =
          (literal * (C * (D / ell ^ 2))) * (1 / logY) := by ring
      _ <=
          (literal * (C * (D / ell ^ 2))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog
          (mul_nonneg hliteralNonneg hscaledCD)
      _ <=
          ((2 * a * Z / ell + 1) * (C * (D / ell ^ 2))) *
            (5 / ell) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hliteral hscaledCD)
            hfiveL
      _ =
          (10 * a * C * D) * (Z / ell ^ 4) +
            (5 * C * D) * (1 / ell ^ 3) := by ring
      _ <=
          (10 * a * C * D) * (Z / ell ^ 3) +
            (5 * C * D) * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hZfour hcoeffMain)
          (mul_le_mul_of_nonneg_left hInvCube hcoeffUnit)
      _ <=
          ((10 * a * C * D) + (5 * C * D)) *
            (Z / ell ^ 3 + 1) := by
        calc
          (10 * a * C * D) * (Z / ell ^ 3) +
              (5 * C * D) * 1 <=
              ((10 * a * C * D) * (Z / ell ^ 3) +
                (5 * C * D) * 1) +
                ((10 * a * C * D) +
                  (5 * C * D) * (Z / ell ^ 3)) :=
            le_add_of_nonneg_right
              (add_nonneg hcoeffMain (mul_nonneg hcoeffUnit hq))
          _ =
              ((10 * a * C * D) + (5 * C * D)) *
                (Z / ell ^ 3 + 1) := by ring
      _ =
          (5 * C * D * (2 * a + 1)) *
            (Z / ell ^ 3 + 1) := by ring
  have hInvL : 5 / ell <= 5 :=
    (div_le_iff₀ hL).2 (by nlinarith [hLone])
  have hendpoint :
      (C / logY) * 1 <=
        (5 * C) * (Z / ell ^ 3 + 1) := by
    calc
      (C / logY) * 1 = C * (1 / logY) := by ring
      _ <= C * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog hC
      _ <= C * 5 :=
        mul_le_mul_of_nonneg_left hInvL hC
      _ = (5 * C) * 1 := by ring
      _ <= (5 * C) * (Z / ell ^ 3 + 1) :=
        mul_le_mul_of_nonneg_left hqOne (by positivity)
  exact
    (add_le_add hfreeze hendpoint).trans_eq (by ring)



/-! ## Generic one-interval assemblers -/





















/-! ## The three fixed deep constants -/













/-! ## Finite three-interval assembly -/



/-! ## Eventual three-interval package -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {Z ell logY literal C D a : Real},
  LE.le.{0} (0 : Real) Z →
    LE.le.{0} (1 : Real) ell →
      LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) ell) logY →
        LE.le.{0} (0 : Real) C →
          LE.le.{0} (0 : Real) D →
            LE.le.{0} (0 : Real) a →
              LE.le.{0} literal
                  (HAdd.hAdd.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) a) Z) ell) (1 : Real)) →
                LE.le.{0} (0 : Real) literal →
                  LE.le.{0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} literal logY) C)
                        (HDiv.hDiv.{0, 0, 0} D (HPow.hPow.{0, 0, 0} ell (2 : Nat))))
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} C logY) (1 : Real)))
                    (HMul.hMul.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (5 : Real) C) D)
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) a) (1 : Real)))
                        (HMul.hMul.{0, 0, 0} (5 : Real) C))
                      (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} ell (3 : Nat))) (1 : Real))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
