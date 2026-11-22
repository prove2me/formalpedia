-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_hasPaperProposition87Conclusion_of_normalizedLawCompanion
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.hasPaperProposition87Conclusion_of_normalizedLawCompanion
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:17:42.960416+00:00
-- url     : https://prove2.me/theorems/9360f043-cba1-4c78-b708-df0b231d3d9d
-- title:
--   Transport of Proposition 8.7 from unit mass to active mass
-- statement:
--   Let $B$ be bridge data on finite head and band sets, with nonempty head set. Let $T$ be a barycentric target and $q>0$, and assume that the baseline of $B$ is the active-mass baseline $qT$. Suppose its normalized-law companion has a Proposition 8.7 path certificate for band displacement $\Delta/q$, marked target $t/q$, size $N/q$, radius $a\ge0$, and constant $C_{\rm post}$, with any finite auxiliary frozen layer and auxiliary integer quota.
--
--   Consider a possibly different finite frozen layer $(v_f,w_f)$ and integer $k$ satisfying $k=\sum_f w_f+B.q$. Suppose $C\ge1$, $B.W>1$, both physical upper endpoints are bounded by the physical bound at $(C,n)$, head patterns are separated, frozen ambient weights lie in $[0,1]$, and frozen and active sample weights are bounded by $C_{\rm fixed}/L$ and $C_{\rm active}/L$. Write $V$ for the valuation-log coefficient at $(C,W)$ and $J$ for the nuisance-statistic coefficient of $B$ at $C$. If
--   $$C_{\rm fixed}+e^{6a(V+J)}C_{\rm active}\le L,$$
--   then $B$ itself has the Proposition 8.7 conclusion for $(\Delta,a,t,N,C_{\rm post})$ with this literal frozen layer and quota $k$.
--
--   This transports a normalized path without requiring any relation between the two frozen layers or integrality of $q-1$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperProposition87ActiveMassTransport.lean#L647-L870

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
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006

universe u_1 u_2 u_3 u_4

theorem Erdos390.Full.PaperBridgeFit.BridgeData.hasPaperProposition87Conclusion_of_normalizedLawCompanion :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head] {Aux : Type u_3}
  {Fixed : Type u_4} [inst_5 : Fintype.{u_3} Aux] [inst_6 : Fintype.{u_4} Fixed]
  (T :
    Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
  (q : Real) (hq : LT.lt.{0} (0 : Real) q),
  Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.activeMassBaseline.{u_1} T q hq) →
    ∀ (Delta : Band → Real) (a : NNReal) (markedTarget : Nat → Real) (N Cpost : Real) (auxValue : Aux → Nat)
      (auxWeight : Aux → Real) (auxQuota : Int),
      Erdos390.Full.PaperBridgeFit.BridgeData.HasPaperProposition87Conclusion.{u_1, u_2, u_3}
          (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedLawCompanion.{u_1, u_2} B T)
          (fun j => HDiv.hDiv.{0, 0, 0} (Delta j) q) a (fun p => HDiv.hDiv.{0, 0, 0} (markedTarget p) q)
          (HDiv.hDiv.{0, 0, 0} N q) Cpost auxValue auxWeight auxQuota →
        ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real) (quota : Int),
          Eq.{1} (↑quota)
              (HAdd.hAdd.{0, 0, 0} (∑ f, fixedWeight f) (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1, u_2} B)) →
            ∀ {C Cfixed Cactive : Real},
              LE.le.{0} (1 : Real) C →
                LT.lt.{0} (1 : Nat)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                      LE.le.{0}
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                        (Erdos390.Full.ArithmeticModel.physicalBound C
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) →
                      (∀ (x : Nat),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_4} fixedValue fixedWeight
                              x)) →
                        (∀
                            (m :
                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                            LE.le.{0}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_4} fixedValue fixedWeight
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                              (HDiv.hDiv.{0, 0, 0} Cfixed (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))) →
                          (∀
                              (m :
                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                              LE.le.{0}
                                (Erdos390.Full.PaperBridgeFit.BaselineAllocation.baseWeight.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B) m)
                                (HDiv.hDiv.{0, 0, 0} Cactive
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))) →
                            LE.le.{0}
                                (HAdd.hAdd.{0, 0, 0} Cfixed
                                  (HMul.hMul.{0, 0, 0}
                                    (Real.exp
                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                        (HMul.hMul.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0}
                                            (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient C
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatisticCoefficient.{u_1,
                                                u_2}
                                              B C))
                                          (HMul.hMul.{0, 0, 0} (3 : Real) ↑a))))
                                    Cactive))
                                (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B) →
                              Erdos390.Full.PaperBridgeFit.BridgeData.HasPaperProposition87Conclusion.{u_1, u_2, u_4} B
                                Delta a markedTarget N Cpost fixedValue fixedWeight quota := by sorry
