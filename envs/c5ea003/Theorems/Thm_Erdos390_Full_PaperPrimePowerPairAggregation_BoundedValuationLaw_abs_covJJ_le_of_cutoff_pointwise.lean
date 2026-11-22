-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerPairAggregation_BoundedValuationLaw_abs_covJJ_le_of_cutoff_pointwise
-- name    : Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.abs_covJJ_le_of_cutoff_pointwise
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:21:31.563564+00:00
-- url     : https://prove2.me/theorems/8d541053-2aa4-4bfb-a875-9c74136f572f
-- title:
--   Geometric aggregation of the double-high covariance
-- statement:
--   Let a bounded-valuation law have physical bound $M$, and let $p,q$ be primes. Write $I_{p,r}=\mathbf1_{p^r\mid m}$ and $J_p=v_p(m)-\mathbf1_{p\mid m}$. Let $R_p=\{2,\ldots,\mathrm{valuationCutoff}(p,M)\}$ and similarly $R_q$. Suppose $K\ge0$ and, for every $r\in R_p,s\in R_q$, $|\operatorname{Cov}(I_{p,r},I_{q,s})|\le K(r+1)(s+1)/(p^rq^s)+e_{r,s}$.
--
--   $$|\operatorname{Cov}(J_p,J_q)|\le\frac{64K}{p^2q^2}+\sum_{r\in R_p}\sum_{s\in R_q}e_{r,s}.$$
--
--   This converts the pointwise double-high estimate into the reciprocal-square scale needed by row contraction.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerPairAggregation.lean#L139-L236

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

universe u_1

theorem Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.abs_covJJ_le_of_cutoff_pointwise :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {p q : Nat},
  Nat.Prime p →
    Nat.Prime q →
      ∀ {K : Real},
        LE.le.{0} (0 : Real) K →
          ∀ (e : Nat → Nat → Real),
            (∀ (r : Nat),
                Membership.mem.{0, 0}
                    (Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                    r →
                  ∀ (s : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.Full.ArithmeticModel.highExponents
                          (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                        s →
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.FiniteProbability.covariance.{u_1}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                        (HAdd.hAdd.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} K
                            (HDiv.hDiv.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real)))
                              (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) (HPow.hPow.{0, 0, 0} (↑q) s))))
                          (e r s))) →
              LE.le.{0} (abs.{0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_1} law p q))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (64 : Real) K)
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))
                  (∑
                    r ∈ Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                    ∑
                      s ∈
                        Erdos390.Full.ArithmeticModel.highExponents (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                      e r s)) := by sorry
