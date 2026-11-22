-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerPairAggregation_BoundedValuationLaw_paperBand_row_le_of_cutoff_pointwise
-- name    : Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:59.528363+00:00
-- url     : https://prove2.me/theorems/44fe6193-4793-43db-a06e-b385184a0878
-- title:
--   From cutoff prime-power estimates to the paper covariance row
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Let a bounded-valuation law have physical bound $M$, with $n>1,W>1$. Let $I_p=\mathbf1_{p\mid m}$, $V_p=v_p(m)$, $I_{p,r}=\mathbf1_{p^r\mid m}$, $t_p=\log p/\log y$, and $R_p=\{2,\ldots,\mathrm{valuationCutoff}(p,M)\}$. Suppose $A,\epsilon\ge0$. For distinct band primes, assume the mixed, reverse-mixed, and double-high covariances are bounded respectively by $(At_pt_q+\epsilon)(r+1)/(p^rq)$, $(At_pt_q+\epsilon)(s+1)/(pq^s)$, and $(At_pt_q+\epsilon)(r+1)(s+1)/(p^rq^s)$, plus errors $e^{JI}_{pqr},e^{IJ}_{pqs},e^{JJ}_{pqrs}$. Assume $\mathbb EI_{p,r}\le(A+\epsilon)(r+1)/p^r+e^D_{pr}$. Suppose the summed errors obey $$p\left[\sum_{q\ne p}\left(\sum_{R_p}e^{JI}_{pqr}+\sum_{R_q}e^{IJ}_{pqs}+\sum_{R_p,R_q}e^{JJ}_{pqrs}\right)+3\sum_{r\in R_p}(2r-3)e^D_{pr}\right]\le R.$$ Let $H_T=\sum_{W<q\le Y}t_q/q$, $H_1=\sum_{W<q\le Y}1/q$, and $C_*$ be the fixed pair-aggregation constant.
--
--   $$p\sum_{W<q\le Y\atop q\ {\rm prime}}|\operatorname{Cov}(V_p,V_q)-\operatorname{Cov}(I_p,I_q)|\le\frac{C_*A(H_T+5)}W+\frac{C_*\epsilon(H_1+5)}W+R.$$
--
--   This is the explicit interface from the four prime-power displays to the full-valuation covariance row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerPairAggregation.lean#L292-L469

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1

theorem Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {n W : Nat},
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ (A epsilon remRow : Real) (eJI eIJ : Nat → Nat → Nat → Real) (eJJ : Nat → Nat → Nat → Nat → Real)
        (eD : Nat → Nat → Real),
        LE.le.{0} (0 : Real) A →
          LE.le.{0} (0 : Real) epsilon →
            (∀ (p : Nat),
                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                  ∀ (q : Nat),
                    Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                      ∀ (r : Nat),
                        Membership.mem.{0, 0}
                            (Erdos390.Full.ArithmeticModel.highExponents
                              (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                            r →
                          LE.le.{0}
                            (abs.{0}
                              (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law q)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                    (Erdos390.Full.ArithmeticModel.tPrime n q))
                                  epsilon)
                                (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                  (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) ↑q)))
                              (eJI p q r))) →
              (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    ∀ (q : Nat),
                      Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                        ∀ (s : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                              s →
                            LE.le.{0}
                              (abs.{0}
                                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law p)
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                      (Erdos390.Full.ArithmeticModel.tPrime n q))
                                    epsilon)
                                  (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real))
                                    (HMul.hMul.{0, 0, 0} (↑p) (HPow.hPow.{0, 0, 0} (↑q) s))))
                                (eIJ p q s))) →
                (∀ (p : Nat),
                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                      ∀ (q : Nat),
                        Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                          ∀ (r : Nat),
                            Membership.mem.{0, 0}
                                (Erdos390.Full.ArithmeticModel.highExponents
                                  (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
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
                                      (HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                            (Erdos390.Full.ArithmeticModel.tPrime n q))
                                          epsilon)
                                        (HDiv.hDiv.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                            (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real)))
                                          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r)
                                            (HPow.hPow.{0, 0, 0} (↑q) s))))
                                      (eJJ p q r s))) →
                  (∀ (p : Nat),
                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                        ∀ (r : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                              r →
                            LE.le.{0}
                              (Erdos390.Full.FiniteProbability.expect.{u_1}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r))
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} A epsilon)
                                  (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                    (HPow.hPow.{0, 0, 0} (↑p) r)))
                                (eD p r))) →
                    (∀ (p : Nat),
                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                          LE.le.{0}
                            (HMul.hMul.{0, 0, 0} (↑p)
                              (HAdd.hAdd.{0, 0, 0}
                                (∑ q ∈ Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p,
                                  HAdd.hAdd.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0}
                                      (∑
                                        r ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                        eJI p q r)
                                      (∑
                                        s ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                        eIJ p q s))
                                    (∑
                                      r ∈
                                        Erdos390.Full.ArithmeticModel.highExponents
                                          (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                      ∑
                                        s ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                        eJJ p q r s))
                                (HMul.hMul.{0, 0, 0} (3 : Real)
                                  (∑
                                    r ∈
                                      Erdos390.Full.ArithmeticModel.highExponents
                                        (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                    HMul.hMul.{0, 0, 0}
                                      (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat))) (eD p r)))))
                            remRow) →
                      ∀ (p : Nat),
                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                          LE.le.{0}
                            (HMul.hMul.{0, 0, 0} (↑p)
                              (∑ q ∈ Erdos390.Full.ArithmeticModel.primeBand n W,
                                abs.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1} law p q)
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1} law p q))))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant A)
                                    (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W) (5 : Real)))
                                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant epsilon)
                                    (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandReciprocalSum n W) (5 : Real)))
                                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W)))
                              remRow) := by sorry
