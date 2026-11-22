-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:26:12.604345+00:00
-- url     : https://prove2.me/theorems/c1d397f6-4a9e-4e1c-acd7-f96a4ce3f97c
-- title:
--   Eventual uniform Schur inverse and quadratic lower bound
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix nonempty finite head and band sets, physical intervals with $1\le I_\sigma^{\rm lower}<I_\sigma^{\rm upper}\le U$, $U\ge1$, a cutoff $W>1$, radius $a\ge0$, and constants $m_0,s,C_f>0$. Let $\epsilon_n\ge0$ satisfy $\epsilon_n\log L_n\to0$. Eventually in $n$, consider any bridge of size $n$ and cutoff $W$ with these physical endpoints and a barycentric target of cell-mass margin at least $m_0$ supplying its baseline. Suppose that throughout the effective ball $\|z\|\le a$ its full projected operator is a continuous linear equivalence with inverse norm at most $C_f$, every band center is at least $s/\log L_n$, and every nuisance-valuation covariance is at most $\epsilon_n/p$ in absolute value. Set $\gamma$ to the canonical nuisance gap for $I,U,3a$ and the target, $r$ to the source nuisance marked Schur rate at $(\epsilon_n,\gamma,s/\log L_n)$, and $C_s=C_f/(1-2C_fr)$. For every point in the ball, the actual band Schur operator $S_z$ is a linear equivalence, and
--
--   $$\|S_z^{-1}v\|_\sharp\le C_s\|v\|_\sharp,\qquad C_s\le2C_f,$$
--   $$\frac{d_{\min}^2}{\Omega C_s}\|q\|_\sharp^2\le\operatorname{Var}_{\mu_z}(\operatorname{Res}_{\rm nuis}Q_q).$$
--
--   Here $\|\cdot\|_\sharp$ is the paper sharp norm, $d_{\min}$ is the source raw diagonal lower weight, $\Omega$ is total sharp weight, and $Q_q$ is the full band-regression score.
--
--   The eventual threshold is uniform in all later bridges and inverse families, and the retained inverse constant is at most twice the full inverse constant.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperSelectedMeshSchurEventually.lean#L29-L224

import Definitions.Def_erdos390_analytic_statement_auxiliaries
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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {U : Real}
  (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
  (W : Nat) (hW : LT.lt.{0} (1 : Nat) W) (a : NNReal) (marginFloor centerScale Cfull : Real),
  LT.lt.{0} (0 : Real) marginFloor →
    LT.lt.{0} (0 : Real) centerScale →
      LT.lt.{0} (0 : Real) Cfull →
        ∀ (epsilon : Nat → Real),
          (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n)) →
            Filter.Tendsto.{0, 0}
                (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0}
                (nhds.{0} (0 : Real)) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band),
                  Eq.{1}
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      n →
                    ∀
                      (hBW :
                        Eq.{1}
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          W)
                      (T :
                        Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                      LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                        ∀
                          (hbaseline :
                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                          (hlo :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (hhi :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (fullEquiv :
                            (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                              Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z →
                                ContinuousLinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                              (hz :
                                Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z)
                              (q :
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                              Eq.{u_2 + 1}
                                ((fullEquiv z hz :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                      ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                  q)
                                ((Erdos390.Full.PaperBridgeFit.BridgeData.actualFullProjectedCLM.{u_1, u_2} B
                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B) →
                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                        z) :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                      ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                  q)) →
                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                (hz :
                                  Membership.mem.{u_1, u_1}
                                    (Metric.closedBall.{u_1}
                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                      (↑a : Real))
                                    z)
                                (v :
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                LE.le.{0}
                                  (Norm.norm.{u_2}
                                    ((ContinuousLinearEquiv.symm.{0, 0, u_2, u_2} (fullEquiv z hz) :
                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                      v))
                                  (HMul.hMul.{0, 0, 0} Cfull (Norm.norm.{u_2} v))) →
                              (∀ (i : Band),
                                  LE.le.{0}
                                    (HDiv.hDiv.{0, 0, 0} centerScale
                                      (Real.log
                                        (Erdos390.Full.Scale.L
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)) →
                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)),
                                    Membership.mem.{u_1, u_1}
                                        (Metric.closedBall.{u_1}
                                          (0 :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (↑a : Real))
                                        z →
                                      ∀
                                        (c :
                                          Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
                                        (p :
                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                        LE.le.{0}
                                          (abs.{0}
                                            (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z))
                                              (fun
                                                  (m :
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)) =>
                                                WithLp.ofLp.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2}
                                                    B m)
                                                  c)
                                              fun
                                                (m :
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                      B)) =>
                                              Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
                                          (HMul.hMul.{0, 0, 0}
                                            (epsilon
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑p : Nat) : Real)))) →
                                  let gamma :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1, u_2} B
                                      I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T;
                                  let rate :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceMarkedSchurRate.{u_1, u_2} B
                                      (epsilon
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                      gamma
                                      (HDiv.hDiv.{0, 0, 0} centerScale
                                        (Real.log
                                          (Erdos390.Full.Scale.L
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))));
                                  let Cschur :=
                                    HDiv.hDiv.{0, 0, 0} Cfull
                                      (HSub.hSub.{0, 0, 0} (1 : Real)
                                        (HMul.hMul.{0, 0, 0} Cfull (HMul.hMul.{0, 0, 0} (2 : Real) rate)));
                                  ∃ (e :
                                    (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                      Membership.mem.{u_1, u_1}
                                          (Metric.closedBall.{u_1}
                                            (0 :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (↑a : Real))
                                          z →
                                        LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                    And
                                      (∀
                                        (z :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                        (hz :
                                          Membership.mem.{u_1, u_1}
                                            (Metric.closedBall.{u_1}
                                              (0 :
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                    B))
                                              (↑a : Real))
                                            z)
                                        (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                        Eq.{u_2 + 1}
                                          ((e z hz :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q)
                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2}
                                                B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                    u_2}
                                                  B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                    u_2}
                                                  B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                  (Decidable.byContradiction
                                                    fun
                                                      (a :
                                                        Not
                                                          (LT.lt.{0} (1 : Nat)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B)))) =>
                                                    Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                        u_2}
                                                      W hW n B hBW a)
                                                  z hz) :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q))
                                      (And
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
                                                (↑a : Real))
                                              z)
                                          (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                          LE.le.{0}
                                            (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                              ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz) :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2}
                                                        B))
                                                v))
                                            (HMul.hMul.{0, 0, 0} Cschur
                                              (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                v)))
                                        (And (LE.le.{0} Cschur (HMul.hMul.{0, 0, 0} (2 : Real) Cfull))
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
                                                  (↑a : Real))
                                                z)
                                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                            LE.le.{0}
                                              (HMul.hMul.{0, 0, 0}
                                                (HDiv.hDiv.{0, 0, 0}
                                                  (HPow.hPow.{0, 0, 0}
                                                    (Erdos390.Full.PaperWeightedInverseExport.rawDLowerWeight.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    (2 : Nat))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    Cschur))
                                                (HPow.hPow.{0, 0, 0}
                                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                    q)
                                                  (2 : Nat)))
                                              (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q)))))) := by sorry
