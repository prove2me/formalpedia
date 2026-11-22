-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
-- name    : Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:19:38.932215+00:00
-- url     : https://prove2.me/theorems/8f3fa7fc-0733-4032-b1eb-2b4b93530803
-- title:
--   Uniform linear head bounds for coherent selector targets
-- statement:
--   Let $c>C_0$ and let $\delta_*$ satisfy the paper combined-charge admissibility condition. Fix depth d, a family threshold N, cutoff $W>0$, and a finite set P of primes at most W. Let F be a guarded tail family such that for every fiber $n\ge N$, its combined selector charge Q divides its precharged target U,
--
--   $$v_p(U)\ge v_p(Q)+\frac{c-C_0}{24(p-1)}\frac n{\log n}\qquad(p\le2d+1\text{ prime}),$$
--
--   and U times its central-anchor divisor equals the central tail product. For its residual selector target $T_n$, eventually uniformly over the family fibers and $p\in P$,
--
--   $$\frac{c-C_0}{48W}\frac n{\log n}\le v_p(T_n)\le\left(\frac c{p-1}+1\right)\frac n{\log n}.$$
--
--   These lower and upper envelopes supply positive head-simplex margins from one coherent combined-charge construction.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor.lean#L148-L463

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds :
∀ {c deltaStar : Real},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    Erdos390.WholePaper.IsPaperCombinedChargeDeltaStar c deltaStar →
      ∀ {depth N W : Nat},
        LT.lt.{0} (0 : Nat) W →
          ∀ (P : Finset.{0} Nat),
            (∀ (p : Nat), Membership.mem.{0, 0} P p → Nat.Prime p) →
              (∀ (p : Nat), Membership.mem.{0, 0} P p → LE.le.{0} p W) →
                ∀ (F : Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily c depth N),
                  (∀ (n : Nat) (hn : LE.le.{0} N n),
                      have R := Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn;
                      have certificate := Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F n hn;
                      And
                        (Dvd.dvd.{0}
                          (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R
                            (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
                          (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate))
                        (And
                          (∀ (p : Nat),
                            Membership.mem.{0, 0}
                                (Erdos390.WholePaper.primesUpTo
                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)))
                                p →
                              LE.le.{0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0)
                                      (HMul.hMul.{0, 0, 0} (24 : Real) ↑(HSub.hSub.{0, 0, 0} p (1 : Nat))))
                                    (Erdos390.WholePaper.secondOrderScale n))
                                  ↑((Nat.factorization
                                        (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R
                                          (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R
                                            deltaStar)))
                                      p))
                                ↑((Nat.factorization
                                      (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget
                                        certificate))
                                    p))
                          (Eq.{1}
                            (HMul.hMul.{0, 0, 0}
                              (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate)
                              (Erdos390.WholePaper.centralAnchorDivisor n
                                (Erdos390.WholePaper.centralAnchorCutoff depth n)
                                (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate)))
                            (Erdos390.WholePaper.centralTailProduct n (Erdos390.WholePaper.upperTailLength c n))))) →
                    ∀ᶠ (n : Nat) in Filter.atTop.{0},
                      ∀ (hn : LE.le.{0} N n) (p : ↥P),
                        And
                          (LE.le.{0}
                            (HMul.hMul.{0, 0, 0}
                              (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
                              (Erdos390.WholePaper.secondOrderScale n))
                            ↑((Nat.factorization
                                  (Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget
                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F n hn)
                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn)
                                    (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn)
                                      deltaStar)))
                                ↑p))
                          (LE.le.{0}
                            (↑((Nat.factorization
                                  (Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget
                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F n hn)
                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn)
                                    (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn)
                                      deltaStar)))
                                ↑p))
                            (HMul.hMul.{0, 0, 0}
                              (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c ↑p)
                              (Erdos390.WholePaper.secondOrderScale n))) := by sorry
