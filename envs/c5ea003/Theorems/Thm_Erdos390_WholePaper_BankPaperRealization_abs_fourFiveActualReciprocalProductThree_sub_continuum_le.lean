-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_fourFiveActualReciprocalProductThree_sub_continuum_le
-- name    : Erdos390.WholePaper.BankPaperRealization.abs_fourFiveActualReciprocalProductThree_sub_continuum_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:51:28.421059+00:00
-- url     : https://prove2.me/theorems/ebe065e3-dabc-42d1-837f-6f2546b72ec9
-- title:
--   Three-coordinate reciprocal-prime product transfer
-- statement:
--   Let $A\le Y$ with $A$ above the reciprocal bounded-variation safe cutoff. For each integer $i\in(A,Y]$, let $a_i$ be the anchored reciprocal-prime atom and $b_i$ its log-log continuum cell atom. Suppose $\sum|a_i|,\sum|b_i|\le M$. Let $K(i,j,k)$ have right discrete bounded-variation norm at most $V\ge0$ in each coordinate, uniformly in the other two. Write $E(A)$ for the one-coordinate reciprocal BV error.
--
--   $$\left|\sum_{i,j,k}K(i,j,k)a_ia_ja_k-\sum_{i,j,k}K(i,j,k)b_ib_jb_k\right|\le3E(A)M^2V.$$
--
--   This is the largest product telescope needed in the four-to-five chamber.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveProductMeasureTelescope.lean#L527-L685

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.abs_fourFiveActualReciprocalProductThree_sub_continuum_le :
∀ (K : Nat → Nat → Nat → Real) {A Y : Nat} {M V : Real},
  LE.le.{0} Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVSafeCutoff A →
    LE.le.{0} A Y →
      LE.le.{0}
          (∑ i ∈ Finset.Ioc.{0} A Y,
            abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveAnchoredReciprocalPrimeAtom A i))
          M →
        LE.le.{0}
            (∑ i ∈ Finset.Ioc.{0} A Y,
              abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveAnchoredLogLogCellAtom A i))
            M →
          (∀ (j : Nat),
              Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) j →
                ∀ (k : Nat),
                  Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) k →
                    LE.le.{0}
                      (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (fun i => K i j k) A Y) V) →
            (∀ (i : Nat),
                Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) i →
                  ∀ (k : Nat),
                    Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) k →
                      LE.le.{0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (fun j => K i j k) A Y)
                        V) →
              (∀ (i : Nat),
                  Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) i →
                    ∀ (j : Nat),
                      Membership.mem.{0, 0} (Finset.Ioc.{0} A Y) j →
                        LE.le.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm (K i j) A Y)
                          V) →
                LE.le.{0} (0 : Real) V →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveActualReciprocalProductThree K A Y)
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumLogLogProductThree K A Y)))
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (3 : Real)
                          (Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVError A))
                        (HPow.hPow.{0, 0, 0} M (2 : Nat)))
                      V) := by sorry
