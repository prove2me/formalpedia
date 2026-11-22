-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:52:08.208728+00:00
-- url     : https://prove2.me/theorems/898c9e42-2639-4f8a-8cbe-887dcdfdc3c7
-- title:
--   Canonical two-stage estimates assemble a physically centered fitting path
-- statement:
--   Let $B$ be bridge data with nonempty finite head and band sets and a finite frozen index set. Its physical intervals lie between $1$ and $U\ge1$, its baseline is a specified barycentric baseline, $W>1$, its head patterns contain exactly the primes at most $W$, and it has prime-log compatibility. Fix a band target $\Delta$, a radius $a\ge0$, and speed $s\ge0$. On the closed effective-parameter ball of radius $a$, assume the actual band Schur map has an inverse bounded by $C_{\rm inv}>0$ in sharp norm and by $C_{\rm ord}\ge0$ in ordinary norm; the compensated slow variance is at least $\gamma w^2$ with $\gamma>0$; its regression-target row is at most $C_{\rm row}w$ times the band center; and compensated prime coefficients are bounded by $C_{\rm comp}$. Suppose the band and slow target sizes are at most $T_b,T_s$, and the fast and slow nuisance covariance vectors are at most the canonical nuisance gap times $C_f,C_s$. The constants $C_{\rm row},T_b,T_s,C_{\rm comp}$ are nonnegative. With harmonic masses $m_j$ and band centers $c_j$, put $Q=(\sum_jm_jc_j)(2C_{\rm inv}C_{\rm row}w)T_b+wT_s$ and $R=Q/(\gamma w^2)$. Require
--   $$C_{\rm ord}T_b+RC_{\rm comp}\le s,\quad C_f+RC_s\le s,\quad wR\le s\le a.$$
--   For a finite set of positive monitored primes, assume the marked covariance along the fitting vector field is bounded on this ball by $C_{\rm row}'/p$, with $C_{\rm row}'\ge0$, total active mass $q\le C_{\rm mass}N$, and initial marked error at most $C_{\rm initial}N/(pL)$. Assume an integer quota equals frozen total mass plus $q$. Finally suppose the head patterns are separated; sample values are bounded by the physical endpoint associated with $C\ge1$; frozen ambient weights belong to $[0,1]$; frozen weights on active samples and active baseline weights have respective bounds $C_{\rm fixed}/L,C_{\rm active}/L$; and
--   $$C_{\rm fixed}+\exp\!\left(6a[\operatorname{valuationLogCoefficient}(C,W)+\operatorname{nuisanceStatisticCoefficient}(C)]\right)C_{\rm active}\le L.$$
--   Then there is a fitting path $\xi:[0,1]\to B.\mathrm{ParamSpace}$ starting at zero, solving the prescribed covariance-inverse vector-field equation, remaining in the effective ball, and satisfying paper effective size at most $3a$. At its endpoint the band moments increase by exactly $\Delta$, while physical, ordinary-log, head-indicator, head-prime valuation, and prime-log moments are unchanged. For every monitored prime,
--   $$|\operatorname{markedTarget}(p)-\operatorname{paperMoment}_{\xi(1)}(v_p)|\le(C_{\rm initial}+C_{\rm mass}C_{\rm row}')\frac{N}{pL}.$$
--   Throughout the path the combined ambient weights stay in $[0,1]$, frozen coordinates remain unchanged, active mass is $q$, and total mass is the quota. This is the finite assembly of the analytic inverse and variance inputs into a feasible centered moment fit.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperProposition87CanonicalTwoStageAssembly.lean#L39-L434

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2 u_3

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_physicallyCenteredFixedPartitionFit_of_canonicalTwoStageOutputs :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] {Fixed : Type u_3} [inst_6 : Fintype.{u_3} Fixed]
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {U : Real} (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
  (hlo :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
  (hhiIntervals :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
  (T :
    Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
  (hbaseline :
    Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
  (hW :
    LT.lt.{0} (1 : Nat)
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
  Erdos390.Full.PaperBridgeFit.BridgeData.HasPrimeLogCompatibility.{u_1, u_2} B →
    (∀ (h : Head) (p : Nat),
        Iff
          (Membership.mem.{0, 0}
            (Erdos390.Full.HeadPattern.Pattern.primes
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.pattern.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) h))
            p)
          (And (Nat.Prime p)
            (LE.le.{0} p
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))) →
      ∀ (Delta : Band → Real) (a speed : NNReal)
        {Cinv CinvOrd gammaSlow CrightRow Tband TslowCoord Ccomp CfastNuisance CslowNuisance : Real},
        LT.lt.{0} (0 : Real) Cinv →
          LE.le.{0} (0 : Real) CinvOrd →
            LT.lt.{0} (0 : Real) gammaSlow →
              LE.le.{0} (0 : Real) CrightRow →
                LE.le.{0} (0 : Real) Tband →
                  LE.le.{0} (0 : Real) TslowCoord →
                    LE.le.{0} (0 : Real) Ccomp →
                      ∀
                        (e :
                          (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                            Membership.mem.{u_1, u_1}
                                (Metric.closedBall.{u_1}
                                  (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) ↑a)
                                z →
                              LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                        (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                            (hz :
                              Membership.mem.{u_1, u_1}
                                (Metric.closedBall.{u_1}
                                  (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) ↑a)
                                z)
                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                            Eq.{u_2 + 1} ((e z hz) q)
                              ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2} B
                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                      u_2}
                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                      u_2}
                                    B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz))
                                q)) →
                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                              (hz :
                                Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    ↑a)
                                  z)
                              (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                              LE.le.{0}
                                (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                  ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz)) v))
                                (HMul.hMul.{0, 0, 0} Cinv
                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                    v))) →
                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                (hz :
                                  Membership.mem.{u_1, u_1}
                                    (Metric.closedBall.{u_1}
                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                      ↑a)
                                    z)
                                (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                LE.le.{0} (Norm.norm.{u_2} ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz)) v))
                                  (HMul.hMul.{0, 0, 0} CinvOrd (Norm.norm.{u_2} v))) →
                              (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                  (hz :
                                    Membership.mem.{u_1, u_1}
                                      (Metric.closedBall.{u_1}
                                        (0 :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                        ↑a)
                                      z),
                                  LE.le.{0}
                                    (HMul.hMul.{0, 0, 0} gammaSlow
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                        (2 : Nat)))
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                        u_2}
                                      B ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                          u_2}
                                        B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                          u_2}
                                        B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                      (e z hz))) →
                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (hz :
                                      Membership.mem.{u_1, u_1}
                                        (Metric.closedBall.{u_1}
                                          (0 :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          ↑a)
                                        z)
                                    (j : Band),
                                    LE.le.{0}
                                      (abs.{0}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedBandCovarianceRow.{u_1, u_2}
                                          B
                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B) z)
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, u_2} B
                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B)
                                              z)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                u_2}
                                              B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                u_2}
                                              B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.slowScore.{u_1, u_2} B))
                                          j))
                                      (HMul.hMul.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0} CrightRow
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B))
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B j))) →
                                  LE.le.{0}
                                      (Norm.norm.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1,
                                            u_2}
                                          B Delta))
                                      Tband →
                                    LE.le.{0}
                                        (abs.{0}
                                          (WithLp.ofLp.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.mainPart.{u_1, u_2} B
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedTarget.{u_1, u_2} B
                                                Delta))
                                            Erdos390.Full.PaperBridgeFit.MainCoord.slow.{u_2}))
                                        TslowCoord →
                                      (∀
                                          (z :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (hz :
                                            Membership.mem.{u_1, u_1}
                                              (Metric.closedBall.{u_1}
                                                (0 :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                        u_2}
                                                      B))
                                                ↑a)
                                              z)
                                          (p :
                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                          LE.le.{0}
                                            (abs.{0}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedCoefficient.{u_1,
                                                  u_2}
                                                B
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                        u_2}
                                                      B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z hz)
                                                  (e z hz))
                                                p))
                                            Ccomp) →
                                        (∀
                                            (z :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (hz :
                                              Membership.mem.{u_1, u_1}
                                                (Metric.closedBall.{u_1}
                                                  (0 :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                          u_2}
                                                        B))
                                                  ↑a)
                                                z),
                                            LE.le.{0}
                                              (Norm.norm.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                        u_2}
                                                      B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B
                                                    ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz))
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.projectedNormalizedTargetBand.{u_1,
                                                          u_2}
                                                        B Delta)))))
                                              (HMul.hMul.{0, 0, 0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1,
                                                    u_2}
                                                  B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                CfastNuisance)) →
                                          (∀
                                              (z :
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                    B))
                                              (hz :
                                                Membership.mem.{u_1, u_1}
                                                  (Metric.closedBall.{u_1}
                                                    (0 :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B))
                                                    ↑a)
                                                  z),
                                              LE.le.{0}
                                                (Norm.norm.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceVector.{u_1,
                                                      u_2}
                                                    B
                                                    ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B)
                                                      z)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandPrimeScore.{u_1,
                                                        u_2}
                                                      B
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1,
                                                          u_2}
                                                        B
                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                              u_2}
                                                            B)
                                                          z)
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                            u_2}
                                                          B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                            u_2}
                                                          B I a hU hlowerOne hupperU hlo hhiIntervals T hbaseline hW z
                                                          hz)
                                                        (e z hz)))))
                                                (HMul.hMul.{0, 0, 0}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) ↑a) T)
                                                  CslowNuisance)) →
                                            LE.le.{0}
                                                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} CinvOrd Tband)
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HDiv.hDiv.{0, 0, 0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                          u_2}
                                                        B
                                                        (HMul.hMul.{0, 0, 0} Cinv
                                                          (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                        Tband TslowCoord)
                                                      (HMul.hMul.{0, 0, 0} gammaSlow
                                                        (HPow.hPow.{0, 0, 0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                          (2 : Nat))))
                                                    Ccomp))
                                                ↑speed →
                                              LE.le.{0}
                                                  (HAdd.hAdd.{0, 0, 0} CfastNuisance
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HDiv.hDiv.{0, 0, 0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                            u_2}
                                                          B
                                                          (HMul.hMul.{0, 0, 0} Cinv
                                                            (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                          Tband TslowCoord)
                                                        (HMul.hMul.{0, 0, 0} gammaSlow
                                                          (HPow.hPow.{0, 0, 0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                            (2 : Nat))))
                                                      CslowNuisance))
                                                  ↑speed →
                                                LE.le.{0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                      (HDiv.hDiv.{0, 0, 0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.twoStageCompensatedTargetBoundOrdinaryFast.{u_1,
                                                            u_2}
                                                          B
                                                          (HMul.hMul.{0, 0, 0} Cinv
                                                            (HMul.hMul.{0, 0, 0} (2 : Real) CrightRow))
                                                          Tband TslowCoord)
                                                        (HMul.hMul.{0, 0, 0} gammaSlow
                                                          (HPow.hPow.{0, 0, 0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                                            (2 : Nat)))))
                                                    ↑speed →
                                                  LE.le.{0} speed a →
                                                    ∀ (monitoredPrimes : Finset.{0} Nat) (Crow : Real),
                                                      LE.le.{0} (0 : Real) Crow →
                                                        (∀ (p : Nat),
                                                            Membership.mem.{0, 0} monitoredPrimes p →
                                                              ∀
                                                                (z :
                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                        u_2}
                                                                      B)),
                                                                Membership.mem.{u_1, u_1}
                                                                    (Metric.closedBall.{u_1}
                                                                      (0 :
                                                                        ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                              u_2}
                                                                            B))
                                                                      ↑a)
                                                                    z →
                                                                  LE.le.{0}
                                                                    (abs.{0}
                                                                      (Erdos390.Full.FiniteExponentialFamily.covariance.{u_1,
                                                                          max u_1 u_2}
                                                                        (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1,
                                                                            max u_1 u_2}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                              u_2}
                                                                            B))
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                            u_2}
                                                                          B p)
                                                                        (fun m =>
                                                                          (Erdos390.Full.FiniteExponentialFamily.score.{u_1,
                                                                                max u_1 u_2}
                                                                              (Erdos390.Full.VectorExponentialFamily.scalarFamily.{u_1,
                                                                                  max u_1 u_2}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                    u_2}
                                                                                  B))
                                                                              m)
                                                                            (Erdos390.Full.VectorExponentialFamily.vectorField.{u_1,
                                                                                max u_1 u_2}
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                  u_2}
                                                                                B)
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.targetVector.{u_1,
                                                                                  u_2}
                                                                                B Delta)
                                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                                    u_2}
                                                                                  B)
                                                                                z)))
                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                              u_2}
                                                                            B)
                                                                          z)))
                                                                    (HDiv.hDiv.{0, 0, 0} Crow ↑p)) →
                                                          ∀ (markedTarget : Nat → Real) (N Cinitial Cmass : Real),
                                                            (∀ (p : Nat),
                                                                Membership.mem.{0, 0} monitoredPrimes p →
                                                                  LT.lt.{0} (0 : Nat) p) →
                                                              LE.le.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1, u_2}
                                                                    B)
                                                                  (HMul.hMul.{0, 0, 0} Cmass N) →
                                                                (∀ (p : Nat),
                                                                    Membership.mem.{0, 0} monitoredPrimes p →
                                                                      LE.le.{0}
                                                                        (abs.{0}
                                                                          (HSub.hSub.{0, 0, 0} (markedTarget p)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                u_2}
                                                                              B
                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                  u_2}
                                                                                B p)
                                                                              (0 :
                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                    u_2}
                                                                                  B))))
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} Cinitial N)
                                                                          (HMul.hMul.{0, 0, 0} (↑p)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                u_2}
                                                                              B)))) →
                                                                  ∀ (fixedValue : Fixed → Nat)
                                                                    (fixedWeight : Fixed → Real) (quota : Int),
                                                                    Eq.{1} (↑quota)
                                                                        (HAdd.hAdd.{0, 0, 0} (∑ f, fixedWeight f)
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1,
                                                                              u_2}
                                                                            B)) →
                                                                      ∀ {C Cfixed Cactive : Real},
                                                                        LE.le.{0} (1 : Real) C →
                                                                          (∀
                                                                              (sigma :
                                                                                Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                              LE.le.{0}
                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                      u_2}
                                                                                    B)
                                                                                  sigma)
                                                                                (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                  C
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                        u_2}
                                                                                      B)))) →
                                                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{u_1}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                    u_2}
                                                                                  B) →
                                                                              (∀ (x : Nat),
                                                                                  Membership.mem.{0, 0}
                                                                                    (Set.Icc.{0} (0 : Real) (1 : Real))
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                      fixedValue fixedWeight x)) →
                                                                                (∀
                                                                                    (m :
                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                            u_2}
                                                                                          B)),
                                                                                    LE.le.{0}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                        fixedValue fixedWeight
                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                              u_2}
                                                                                            B)
                                                                                          m))
                                                                                      (HDiv.hDiv.{0, 0, 0} Cfixed
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                            u_2}
                                                                                          B))) →
                                                                                  (∀
                                                                                      (m :
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                              u_2}
                                                                                            B)),
                                                                                      LE.le.{0}
                                                                                        (Erdos390.Full.PaperBridgeFit.BaselineAllocation.baseWeight.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1,
                                                                                              u_2}
                                                                                            B)
                                                                                          m)
                                                                                        (HDiv.hDiv.{0, 0, 0} Cactive
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                              u_2}
                                                                                            B))) →
                                                                                    LE.le.{0}
                                                                                        (HAdd.hAdd.{0, 0, 0} Cfixed
                                                                                          (HMul.hMul.{0, 0, 0}
                                                                                            (Real.exp
                                                                                              (HMul.hMul.{0, 0, 0}
                                                                                                (2 : Real)
                                                                                                (HMul.hMul.{0, 0, 0}
                                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                                    (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                                                                                                      C
                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                                            u_2}
                                                                                                          B)))
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatisticCoefficient.{u_1,
                                                                                                        u_2}
                                                                                                      B C))
                                                                                                  (HMul.hMul.{0, 0, 0}
                                                                                                    (3 : Real) ↑a))))
                                                                                            Cactive))
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                            u_2}
                                                                                          B) →
                                                                                      ∃ path,
                                                                                        And
                                                                                          (Eq.{max (u_1 + 1) (u_2 + 1)}
                                                                                            (path (0 : Real))
                                                                                            (0 :
                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                  u_2}
                                                                                                B))
                                                                                          (And
                                                                                            (∀ (t : Real),
                                                                                              Membership.mem.{0, 0}
                                                                                                  (Set.Icc.{0}
                                                                                                    (0 : Real)
                                                                                                    (1 : Real))
                                                                                                  t →
                                                                                                Membership.mem.{u_1,
                                                                                                    u_1}
                                                                                                  (Metric.closedBall.{u_1}
                                                                                                    (0 :
                                                                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                                                                            u_2}
                                                                                                          B))
                                                                                                    ↑a)
                                                                                                  ((ContinuousLinearEquiv.symm.{0,
                                                                                                        0, u_1,
                                                                                                        max u_1 u_2}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                                                                          u_2}
                                                                                                        B))
                                                                                                    (path t)))
                                                                                            (And
                                                                                              (∀ (t : Real),
                                                                                                Membership.mem.{0, 0}
                                                                                                    (Set.Icc.{0}
                                                                                                      (0 : Real)
                                                                                                      (1 : Real))
                                                                                                    t →
                                                                                                  LE.le.{0}
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.paperEffectiveSize.{u_1,
                                                                                                        u_2}
                                                                                                      B (path t))
                                                                                                    (HMul.hMul.{0, 0, 0}
                                                                                                      (3 : Real) ↑a))
                                                                                              (And
                                                                                                (∀ (t : Real),
                                                                                                  Membership.mem.{0, 0}
                                                                                                      (Set.Icc.{0}
                                                                                                        (0 : Real)
                                                                                                        (1 : Real))
                                                                                                      t →
                                                                                                    HasDerivWithinAt.{0,
                                                                                                        max u_1 u_2}
                                                                                                      path
                                                                                                      (Erdos390.Full.VectorExponentialFamily.vectorField.{u_1,
                                                                                                          max u_1 u_2}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.targetVector.{u_1,
                                                                                                            u_2}
                                                                                                          B Delta)
                                                                                                        (path t))
                                                                                                      (Set.Icc.{0}
                                                                                                        (0 : Real)
                                                                                                        (1 : Real))
                                                                                                      t)
                                                                                                (And
                                                                                                  (∀ (j : Band),
                                                                                                    Eq.{1}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandScore.{u_1,
                                                                                                            u_2}
                                                                                                          B j)
                                                                                                        (path
                                                                                                          (1 : Real)))
                                                                                                      (HAdd.hAdd.{0, 0,
                                                                                                          0}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.bandScore.{u_1,
                                                                                                              u_2}
                                                                                                            B j)
                                                                                                          (0 :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                u_2}
                                                                                                              B))
                                                                                                        (Delta j)))
                                                                                                  (And
                                                                                                    (Eq.{1}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (path
                                                                                                          (1 : Real)))
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                          u_2}
                                                                                                        B
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1,
                                                                                                            u_2}
                                                                                                          B)
                                                                                                        (0 :
                                                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                              u_2}
                                                                                                            B)))
                                                                                                    (And
                                                                                                      (Eq.{1}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.ordinaryLogScore.{u_1,
                                                                                                              u_2}
                                                                                                            B)
                                                                                                          (path
                                                                                                            (1 : Real)))
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                            u_2}
                                                                                                          B
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.ordinaryLogScore.{u_1,
                                                                                                              u_2}
                                                                                                            B)
                                                                                                          (0 :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                u_2}
                                                                                                              B)))
                                                                                                      (And
                                                                                                        (∀
                                                                                                          (h :
                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1,
                                                                                                                u_2}
                                                                                                              B),
                                                                                                          Eq.{1}
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                u_2}
                                                                                                              B
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.headIndicator.{u_1,
                                                                                                                  u_2}
                                                                                                                B ↑h)
                                                                                                              (path
                                                                                                                (1 :
                                                                                                                  Real)))
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                u_2}
                                                                                                              B
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.headIndicator.{u_1,
                                                                                                                  u_2}
                                                                                                                B ↑h)
                                                                                                              (0 :
                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)))
                                                                                                        (And
                                                                                                          (∀ (p : Nat),
                                                                                                            Nat.Prime
                                                                                                                p →
                                                                                                              LE.le.{0}
                                                                                                                  p
                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                                                                        u_2}
                                                                                                                      B)) →
                                                                                                                Eq.{1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                      u_2}
                                                                                                                    B
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                        u_2}
                                                                                                                      B
                                                                                                                      p)
                                                                                                                    (path
                                                                                                                      (1 :
                                                                                                                        Real)))
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                      u_2}
                                                                                                                    B
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                        u_2}
                                                                                                                      B
                                                                                                                      p)
                                                                                                                    (0 :
                                                                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                          u_2}
                                                                                                                        B)))
                                                                                                          (And
                                                                                                            (Eq.{1}
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                  u_2}
                                                                                                                B
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.primeLogScore.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)
                                                                                                                (path
                                                                                                                  (1 :
                                                                                                                    Real)))
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                  u_2}
                                                                                                                B
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.primeLogScore.{u_1,
                                                                                                                    u_2}
                                                                                                                  B)
                                                                                                                (0 :
                                                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                      u_2}
                                                                                                                    B)))
                                                                                                            (And
                                                                                                              (∀
                                                                                                                (p :
                                                                                                                  Nat),
                                                                                                                Membership.mem.{0,
                                                                                                                      0}
                                                                                                                    monitoredPrimes
                                                                                                                    p →
                                                                                                                  LE.le.{0}
                                                                                                                    (abs.{0}
                                                                                                                      (HSub.hSub.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (markedTarget
                                                                                                                          p)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.paperMoment.{u_1,
                                                                                                                            u_2}
                                                                                                                          B
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.markedValuation.{u_1,
                                                                                                                              u_2}
                                                                                                                            B
                                                                                                                            p)
                                                                                                                          (path
                                                                                                                            (1 :
                                                                                                                              Real)))))
                                                                                                                    (HDiv.hDiv.{0,
                                                                                                                        0,
                                                                                                                        0}
                                                                                                                      (HMul.hMul.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (HAdd.hAdd.{0,
                                                                                                                            0,
                                                                                                                            0}
                                                                                                                          Cinitial
                                                                                                                          (HMul.hMul.{0,
                                                                                                                              0,
                                                                                                                              0}
                                                                                                                            Cmass
                                                                                                                            Crow))
                                                                                                                        N)
                                                                                                                      (HMul.hMul.{0,
                                                                                                                          0,
                                                                                                                          0}
                                                                                                                        (↑p)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1,
                                                                                                                            u_2}
                                                                                                                          B))))
                                                                                                              (And
                                                                                                                (∀
                                                                                                                  (t :
                                                                                                                    Real),
                                                                                                                  Membership.mem.{0,
                                                                                                                        0}
                                                                                                                      (Set.Icc.{0}
                                                                                                                        (0 :
                                                                                                                          Real)
                                                                                                                        (1 :
                                                                                                                          Real))
                                                                                                                      t →
                                                                                                                    ∀
                                                                                                                      (x :
                                                                                                                        Nat),
                                                                                                                      Membership.mem.{0,
                                                                                                                          0}
                                                                                                                        (Set.Icc.{0}
                                                                                                                          (0 :
                                                                                                                            Real)
                                                                                                                          (1 :
                                                                                                                            Real))
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.ambientCombinedWeight.{u_1,
                                                                                                                            u_2}
                                                                                                                          B
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_3}
                                                                                                                            fixedValue
                                                                                                                            fixedWeight)
                                                                                                                          (path
                                                                                                                            t)
                                                                                                                          x))
                                                                                                                (And
                                                                                                                  (∀
                                                                                                                    (t :
                                                                                                                      Real),
                                                                                                                    Membership.mem.{0,
                                                                                                                          0}
                                                                                                                        (Set.Icc.{0}
                                                                                                                          (0 :
                                                                                                                            Real)
                                                                                                                          (1 :
                                                                                                                            Real))
                                                                                                                        t →
                                                                                                                      ∀
                                                                                                                        (f :
                                                                                                                          Fixed),
                                                                                                                        Eq.{1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                              u_2,
                                                                                                                              u_3}
                                                                                                                            B
                                                                                                                            fixedWeight
                                                                                                                            (path
                                                                                                                              t)
                                                                                                                            (Sum.inl.{u_3,
                                                                                                                                u_1}
                                                                                                                              f))
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                              u_2,
                                                                                                                              u_3}
                                                                                                                            B
                                                                                                                            fixedWeight
                                                                                                                            (0 :
                                                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1,
                                                                                                                                  u_2}
                                                                                                                                B)
                                                                                                                            (Sum.inl.{u_3,
                                                                                                                                u_1}
                                                                                                                              f)))
                                                                                                                  (And
                                                                                                                    (∀
                                                                                                                      (t :
                                                                                                                        Real),
                                                                                                                      Membership.mem.{0,
                                                                                                                            0}
                                                                                                                          (Set.Icc.{0}
                                                                                                                            (0 :
                                                                                                                              Real)
                                                                                                                            (1 :
                                                                                                                              Real))
                                                                                                                          t →
                                                                                                                        Eq.{1}
                                                                                                                          (∑
                                                                                                                            m,
                                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.activeCoordinateWeight.{u_1,
                                                                                                                                u_2}
                                                                                                                              B
                                                                                                                              (path
                                                                                                                                t)
                                                                                                                              m)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1,
                                                                                                                              u_2}
                                                                                                                            B))
                                                                                                                    (∀
                                                                                                                      (t :
                                                                                                                        Real),
                                                                                                                      Membership.mem.{0,
                                                                                                                            0}
                                                                                                                          (Set.Icc.{0}
                                                                                                                            (0 :
                                                                                                                              Real)
                                                                                                                            (1 :
                                                                                                                              Real))
                                                                                                                          t →
                                                                                                                        Eq.{1}
                                                                                                                          (∑
                                                                                                                            x,
                                                                                                                            Erdos390.Full.PaperBridgeFit.BridgeData.combinedWeight.{u_1,
                                                                                                                                u_2,
                                                                                                                                u_3}
                                                                                                                              B
                                                                                                                              fixedWeight
                                                                                                                              (path
                                                                                                                                t)
                                                                                                                              x)
                                                                                                                          ↑quota)))))))))))))) := by sorry
