-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerGenericAggregation_primePowerTransferBounds_of_pointwise
-- name    : Erdos390.Full.PaperPrimePowerGenericAggregation.primePowerTransferBounds_of_pointwise
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:04:11.576101+00:00
-- url     : https://prove2.me/theorems/c9e17108-9abd-47a4-b461-31ba11d19701
-- title:
--   Finite aggregation of pointwise prime-power covariance bounds
-- statement:
--   For a finite bounded valuation law, write $I_{p,r}=1_{p^r\mid m}$, $I_p=I_{p,1}$, $V_p=v_p(m)$, and $J_p=V_p-I_p$. Write $t_p=\log p/\log y(n)$ and let all prime sums range over the moving band $\mathcal P_{n,W}$. The five prime-power transfer estimates with constants $(C,R)$ mean: the sums of absolute covariances of $(I_{p,r},I_q)$, $(I_p,I_{q,s})$, and $(I_{p,r},I_{q,s})$ over higher exponents have bounds $(Ct_pt_q+R)/(p^2q)$, $(Ct_pt_q+R)/(pq^2)$, and $(Ct_pt_q+R)/(p^2q^2)$, respectively; also $\mathbb E J_p^2\le(C+R)/p^2$ and $p\sum_q|\operatorname{Cov}(V_p,V_q)-\operatorname{Cov}(I_p,I_q)|\le C/W+R$. Higher exponents run from $2$ to the valuation cutoff determined by the value bound $M$. Assume $n,W>1$ and nonnegative $C_0,E,T_\ell,T_q,T_d,T_r$. For distinct band primes, assume the three pointwise covariance bounds have main coefficients $C_0t_pt_q+E$, weights $(r+1)/(p^rq)$, $(s+1)/(pq^s)$, $(r+1)(s+1)/(p^rq^s)$, and residuals $e_{JI},e_{IJ},e_{JJ}$. Assume $\mathbb E I_{p,r}\le(C_0+E)(r+1)/p^r+e_D(p,r)$. Require the exponent sums of the three residuals to be at most $T_\ell/(p^2q)$, $T_\ell/(pq^2)$, and $T_q/(p^2q^2)$; require $\sum_r(2r-3)e_D(p,r)\le T_d/p^2$. Finally require $p$ times the sum of the off-diagonal residual sums plus three times this diagonal residual sum to be at most $T_r$, and $\sum_p t_p/p\le2\log4$. Then all five transfer estimates hold with
--   $$C=A_{\rm agg}C_0(2\log4+5),\quad R=A_{\rm agg}E+T_\ell+T_q+T_d+A_{\rm agg}E\frac{\sum_p1/p+5}{W}+T_r.$$
--   This separates finite summation from the analytic origin of the pointwise bounds.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerGenericAggregation.lean#L50-L309

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1

theorem Erdos390.Full.PaperPrimePowerGenericAggregation.primePowerTransferBounds_of_pointwise :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {Cmain E Tlin Tquad Tdiag Trow : Real}
  {eJI eIJ : Nat → Nat → Nat → Real} {eJJ : Nat → Nat → Nat → Nat → Real} {eD : Nat → Nat → Real},
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      LE.le.{0} (0 : Real) Cmain →
        LE.le.{0} (0 : Real) E →
          LE.le.{0} (0 : Real) Tlin →
            LE.le.{0} (0 : Real) Tquad →
              LE.le.{0} (0 : Real) Tdiag →
                LE.le.{0} (0 : Real) Trow →
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
                                          (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                          (Erdos390.Full.ArithmeticModel.tPrime n q))
                                        E)
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
                                            (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                            (Erdos390.Full.ArithmeticModel.tPrime n q))
                                          E)
                                        (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real))
                                          (HMul.hMul.{0, 0, 0} (↑p) (HPow.hPow.{0, 0, 0} (↑q) s))))
                                      (eIJ p q s))) →
                      (∀ (p : Nat),
                          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                            ∀ (q : Nat),
                              Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p)
                                  q →
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
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1}
                                                law)
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q
                                                s)))
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} Cmain (Erdos390.Full.ArithmeticModel.tPrime n p))
                                                  (Erdos390.Full.ArithmeticModel.tPrime n q))
                                                E)
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
                                      (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} Cmain E)
                                        (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                          (HPow.hPow.{0, 0, 0} (↑p) r)))
                                      (eD p r))) →
                          (∀ (p : Nat),
                              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                ∀ (q : Nat),
                                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                    LE.le.{0}
                                      (∑
                                        r ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                        eJI p q r)
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} Tlin
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                                        (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q))) →
                            (∀ (p : Nat),
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  ∀ (q : Nat),
                                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                      LE.le.{0}
                                        (∑
                                          s ∈
                                            Erdos390.Full.ArithmeticModel.highExponents
                                              (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                          eIJ p q s)
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} Tlin (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p))
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))) →
                              (∀ (p : Nat),
                                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                    ∀ (q : Nat),
                                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) q →
                                        LE.le.{0}
                                          (∑
                                            r ∈
                                              Erdos390.Full.ArithmeticModel.highExponents
                                                (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                            ∑
                                              s ∈
                                                Erdos390.Full.ArithmeticModel.highExponents
                                                  (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                              eJJ p q r s)
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} Tquad
                                              (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                                            (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat)))) →
                                (∀ (p : Nat),
                                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                      LE.le.{0}
                                        (∑
                                          r ∈
                                            Erdos390.Full.ArithmeticModel.highExponents
                                              (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                          HMul.hMul.{0, 0, 0}
                                            (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                                            (eD p r))
                                        (HMul.hMul.{0, 0, 0} Tdiag
                                          (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))) →
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
                                                    (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                                                    (eD p r)))))
                                          Trow) →
                                    LE.le.{0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W)
                                        (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real))) →
                                      Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_1} law n W
                                        (HMul.hMul.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant Cmain)
                                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real)))
                                            (5 : Real)))
                                        (Erdos390.Full.PaperPrimePowerGenericAggregation.genericAggregationRemainder E
                                          Tlin Tquad Tdiag Trow n W) := by sorry
