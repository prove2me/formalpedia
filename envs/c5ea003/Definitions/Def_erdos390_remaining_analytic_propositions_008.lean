-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_008
-- name    : erdos390_remaining_analytic_propositions_008
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:43:53.981108+00:00
-- url     : https://prove2.me/theorems/9b4214be-e46c-4764-a8af-2330f6c744e3
-- title:
--   Analytic construction propositions, part 8
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus, abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq, bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder, eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower, eventually_bankPaperCanonicalSectionNineBudgetClosure, eventually_roughCanonicalActiveIntrinsicRawBroadSurplus, eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active, eventually_roughCanonical_activeRawBroadPool_linear_lower, eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses, exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar, exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve, exists_eventually_centralAnchorCertificate, exists_uniform_roughFixedHead_friableCount_shift_bound, roughCanonicalBalancedDickmanTransitionLedger_le, roughCanonicalBalancedSaiasTransitionBudget_le, roughCanonicalBalancedSharpFixedHeadBudget_le, roughCanonical_dickmanEndpointMain_sub_lower, roughCanonical_headFreeSmoothInterval_lower_of_shift, roughCompactBV_translation_le_of_le, roughFriableContinuousFixedDivisorDefect_sub_abs_le, roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation, roughFriableMain_abs_le_with_balanceError, roughFriableMain_fixedDivisorShift, roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log, roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common, roughSaiasDickmanCorrection_difference_abs_le, roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le, roughSaiasIntervalFixedDivisorShiftBudget_sharp_le, roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect, roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents, roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq, roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff, sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector, sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log, sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola, sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq, sum_roughSaiasSelectorCellLedger_mul_fourth_le, tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds, tangentOrderedPairEndpointBudget_div_le_densityCoefficients, tangentRoughHeadCandidateMain_normalized_ge_three_quarters.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT
universe u_1 u_2
set_option maxRecDepth 10000
set_option maxHeartbeats 0


noncomputable def Erdos390.RemainingAnalyticGoal008_001 : Prop :=
∀ {V : Type u_1} [inst : Fintype.{u_1} V] [inst_1 : DecidableEq.{u_1 + 1} V] {c : Real} {depth n M : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R : Erdos390.WholePaper.BankPaperRealization n M) (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed) (fixedExceptional : Finset.{0} Nat)
  (K h Phead X0 : Nat) (label : V → Nat) (residual portLoad : V → Real) (cutTraffic : Real) (vertexFlow : V → V → Real),
  (∀ (source target : V), LE.le.{0} (0 : Real) (vertexFlow source target)) →
    (∀ (v : V), Eq.{1} (Erdos390.WholePaper.tangentFlowDivergence.{u_1} vertexFlow v) (residual v)) →
      (∀ {source target : V}, LT.lt.{0} (0 : Real) (vertexFlow source target) → Ne.{u_1 + 1} source target) →
        LE.le.{0} (Erdos390.WholePaper.tangentFlowTraffic.{u_1} vertexFlow) (Erdos390.WholePaper.tangentDistributedTotalTrafficLedger.{u_1} residual cutTraffic) →
          (∀ (v : V),
              LE.le.{0}
                (Erdos390.WholePaper.tangentIncidentFlowMass.{u_1, 0} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label)
                  (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label) (fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2) (label v))
                (HAdd.hAdd.{0, 0, 0} (abs.{0} (residual v)) (HMul.hMul.{0, 0, 0} (2 : Real) (portLoad v)))) →
            Function.Injective.{u_1 + 1, 1} label →
              (∀ (v : V), Nat.Prime (label v)) →
                ∀ (weightedResidual weightedPort : Real),
                  (∀ (v : V), LE.le.{0} (HMul.hMul.{0, 0, 0} (↑(label v) : Real) (abs.{0} (residual v))) weightedResidual) →
                    (∀ (v : V), LE.le.{0} (HMul.hMul.{0, 0, 0} (↑(label v) : Real) (portLoad v)) weightedPort) →
                      ∀ (labelUpper : Nat) (density : Real),
                        LT.lt.{0} (0 : Nat) n →
                          LT.lt.{0} (0 : Real) density →
                            (∀ (v : V), LE.le.{0} (label v) labelUpper) →
                              LE.le.{0} (α := Real) (↑labelUpper : Real) (↑n : Real) →
                                LE.le.{0} (HPow.hPow.{0, 0, 0} (α := Real) (↑labelUpper : Real) (2 : Nat)) (↑n : Real) →
                                  ∀ {L sigma N : Real},
                                    LT.lt.{0} (0 : Real) L →
                                      LT.lt.{0} (0 : Real) sigma →
                                        LT.lt.{0} (0 : Real) N →
                                          Eq.{1} (HMul.hMul.{0, 0, 0} L N) (↑n : Real) →
                                            ∀ (trafficConstant incidentConstant tangentConstant width trafficError incidentError : Real),
                                              LE.le.{0} (Erdos390.WholePaper.tangentDistributedTotalTrafficLedger.{u_1} residual cutTraffic)
                                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} trafficConstant tangentConstant) N) width)
                                                    (HMul.hMul.{0, 0, 0} trafficError N)) →
                                                LE.le.{0} (HAdd.hAdd.{0, 0, 0} weightedResidual (HMul.hMul.{0, 0, 0} (2 : Real) weightedPort))
                                                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} incidentConstant tangentConstant) N) width)
                                                      (HMul.hMul.{0, 0, 0} incidentError N)) →
                                                  LE.le.{0} (Erdos390.WholePaper.tangentDistributedPaperMainBudget trafficConstant incidentConstant tangentConstant width sigma)
                                                      (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (48 : Real)) →
                                                    LE.le.{0} (Erdos390.WholePaper.tangentDistributedPaperErrorBudget trafficError incidentError sigma)
                                                        (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (96 : Real)) →
                                                      LE.le.{0} (Erdos390.WholePaper.tangentDistributedPaperCeilingBudget n labelUpper (Erdos390.WholePaper.tangentDistributedSupportCount.{u_1} V))
                                                          (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (96 : Real)) →
                                                        ∀
                                                          (lowerCard :
                                                            (Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2) →
                                                              Nat),
                                                          (∀
                                                              (request :
                                                                Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                  fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2),
                                                              LT.lt.{0} (0 : Nat) (lowerCard request)) →
                                                            (∀
                                                                (request :
                                                                  Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                    fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2),
                                                                LE.le.{0} (lowerCard request)
                                                                  (Finset.card.{0}
                                                                    (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow)
                                                                      (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label) (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label) L sigma
                                                                      (fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2) n K h Phead X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                                      (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                                      (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request))) →
                                                              (∀
                                                                  (request :
                                                                    Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                      fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2)
                                                                  (side : Erdos390.WholePaper.TangentEndpointSide),
                                                                  LE.le.{0} (HMul.hMul.{0, 0, 0} density (↑n : Real))
                                                                    (HMul.hMul.{0, 0, 0} (α := Real) (↑(lowerCard request) : Real)
                                                                      (↑(Erdos390.WholePaper.tangentEndpointLabel.{u_1}
                                                                            (Erdos390.WholePaper.tangentSplitRequestSource.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label))
                                                                            (Erdos390.WholePaper.tangentSplitRequestTarget.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label)) side
                                                                            request) :
                                                                        Real))) →
                                                                And (∀ (v : V), Eq.{1} (Erdos390.WholePaper.tangentFlowDivergence.{u_1} vertexFlow v) (residual v))
                                                                  (And
                                                                    (∀ (p : Nat),
                                                                      Eq.{1} (α := Real)
                                                                        (∑ request :
                                                                          Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                            fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2,
                                                                          HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.tangentSplitRequestWeight.{u_1} request)
                                                                            (HSub.hSub.{0, 0, 0} (α := Real)
                                                                              (↑((Nat.factorization
                                                                                        (Erdos390.WholePaper.tangentSplitRequestSource.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label)
                                                                                          request) :
                                                                                      (a : Nat) → Nat)
                                                                                    p) :
                                                                                Real)
                                                                              (↑((Nat.factorization
                                                                                        (Erdos390.WholePaper.tangentSplitRequestTarget.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label)
                                                                                          request) :
                                                                                      (a : Nat) → Nat)
                                                                                    p) :
                                                                                Real)))
                                                                        (∑ v : V, HMul.hMul.{0, 0, 0} (residual v) (↑((Nat.factorization (label v) : (a : Nat) → Nat) p) : Real)))
                                                                    (∃ (multiplier :
                                                                      (Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                          fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2) →
                                                                        Nat),
                                                                      And
                                                                        (∀
                                                                          (request :
                                                                            Erdos390.WholePaper.TangentSplitRequest.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                              fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2),
                                                                          Membership.mem.{0, 0}
                                                                            (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow)
                                                                              (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label) (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label) L sigma
                                                                              (fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2) n K h Phead X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request)
                                                                            (multiplier request))
                                                                        (Erdos390.WholePaper.TangentEndpointsDistinct.{u_1}
                                                                          (Erdos390.WholePaper.tangentSplitRequests.{u_1} (Erdos390.WholePaper.tangentPositiveFlowEdges.{u_1} vertexFlow) L sigma
                                                                            fun (edge : Prod.{u_1, u_1} V V) => vertexFlow edge.1 edge.2)
                                                                          (Erdos390.WholePaper.tangentSplitRequestSource.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeSource.{u_1} label))
                                                                          (Erdos390.WholePaper.tangentSplitRequestTarget.{u_1, 0} (Erdos390.WholePaper.tangentStarEdgeTarget.{u_1} label)) multiplier)))

noncomputable def Erdos390.RemainingAnalyticGoal008_002 : Prop :=
∀ {X a b : Nat},
  LT.lt.{0} (0 : Nat) X →
    LE.le.{0} (3 : Nat) a →
      LE.le.{0} a b →
        LE.le.{0} b X →
          LE.le.{0} b (HAdd.hAdd.{0, 0, 0} (Nat.sqrt X) (1 : Nat)) →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
              LE.le.{0} (abs.{0} (∑ m ∈ Finset.Ico.{0} a b, Erdos390.WholePaper.roughSaiasFullyRealNaturalBuchstabCellRemainder X m))
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (40 : Real) (↑X : Real)) (HPow.hPow.{0, 0, 0} (Real.log (↑a : Real)) (2 : Nat)))

noncomputable def Erdos390.RemainingAnalyticGoal008_003 : Prop :=
∀ (cMesh : Real) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank),
  Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderStatement.{u_1, u_2} cMesh I U Cprom Cbank ledger

noncomputable def Erdos390.RemainingAnalyticGoal008_004 : Prop :=
∀ (W K : Nat) {c : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      LE.le.{0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalRawBroadPoolDensity W) (↑n : Real))
        (↑(Finset.card.{0} (Erdos390.WholePaper.bankPaperCanonicalRawSmoothBasePool W n (Erdos390.WholePaper.upperTailLength c n) K)) : Real)

noncomputable def Erdos390.RemainingAnalyticGoal008_005 : Prop :=
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  (B : Nat → Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) (W K0 depth : Nat) {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
  (hdelta : LT.lt.{0} (0 : Real) delta),
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (1 : Real) r0 →
      LT.lt.{0} r0 (3 / 2 : Real) →
        LT.lt.{0} (0 : Real) deltaStar →
          LT.lt.{0} deltaStar (1 / 18 : Real) →
            LT.lt.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (80 : Real) Erdos390.WholePaper.tangentSelbergCanonicalMainConstant) deltaStar) (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
              LE.le.{0} (2 : Nat) W →
                LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
                  LT.lt.{0} (1 : Real) rho →
                    LT.lt.{0} (HPow.hPow.{0, 0, 0} rho (3 : Nat)) r0 →
                      LT.lt.{0} (0 : Real) tangentConstant →
                        LT.lt.{0} (0 : Real) sigma →
                          LE.le.{0} (HAdd.hAdd.{0, 0, 0} delta (Erdos390.Full.RegularRelativeMesh.Mesh.ratio M))
                              (Erdos390.WholePaper.bankPaperCanonicalRatioCellPaperWidthChoice (Erdos390.WholePaper.tangentPaperCleanListDensity W r0) sigma rho tangentConstant) →
                            LE.le.{0} (0 : Real) Cpost →
                              LE.le.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 / 9 : Real) Cpost) Cq) tangentConstant →
                                (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                    And (Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} (B n))) n)
                                      (Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} (B n))) W)) →
                                  (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                      LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1, 0} (B n)) (HMul.hMul.{0, 0, 0} Cq (Erdos390.WholePaper.secondOrderScale n))) →
                                    ∀ᶠ (n : Nat) in Filter.atTop.{0},
                                      ∀ (hn : LT.lt.{0} (1 : Nat) n) (hW : Ne.{1} W (0 : Nat))
                                        (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
                                        (certificate :
                                          Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
                                            (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R) (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                        (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W) (endpoint : Nat → Real),
                                        Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure.{u_1} M (B n) (K0 := K0) R certificate deltaStar sigma hdelta hn hW S r0 rho tangentConstant
                                          Cpost endpoint

noncomputable def Erdos390.RemainingAnalyticGoal008_006 : Prop :=
∀ (W K poolMinimum : Nat) {c deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0}, Erdos390.WholePaper.RoughCanonicalActiveIntrinsicRawBroadSurplus W n (Erdos390.WholePaper.upperTailLength c n) K (3 : Nat) poolMinimum deltaStar

noncomputable def Erdos390.RemainingAnalyticGoal008_007 : Prop :=
∀ (W K0 : Nat) {c beta deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀
          (row :
            Erdos390.WholePaper.CanonicalCompleteRoughRow (Erdos390.Full.ArithmeticModel.yNat n)
              (Erdos390.WholePaper.roughRawCandidateSet n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)))),
          Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar (↑row : Nat) →
            LE.le.{0}
              (abs.{0}
                (Erdos390.WholePaper.roughCanonicalRawRowQuotaError W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.Full.ArithmeticModel.yNat n)
                  (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n)) beta
                  (Erdos390.Full.Scale.L n) row))
              (HMul.hMul.{0, 0, 0} (3 : Real)
                (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta)
                  (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(HDiv.hDiv.{0, 0, 0} n (↑row : Nat)) : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real))))

noncomputable def Erdos390.RemainingAnalyticGoal008_008 : Prop :=
∀ (W K : Nat) {c deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀ (label : Nat),
          Erdos390.WholePaper.IsCompleteRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) label →
            Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar label →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalRawBroadPoolDensity W) (↑(HDiv.hDiv.{0, 0, 0} n label) : Real))
                (↑(Finset.card.{0} (Erdos390.WholePaper.roughCanonicalBroadCorrectionPool W n (Erdos390.WholePaper.upperTailLength c n) K (Erdos390.Full.ArithmeticModel.yNat n) label)) : Real)

noncomputable def Erdos390.RemainingAnalyticGoal008_009 : Prop :=
∀ (W K : Nat) {c r0 deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (1 : Real) r0 →
      LT.lt.{0} r0 (3 / 2 : Real) →
        LT.lt.{0} (0 : Real) deltaStar →
          LT.lt.{0} deltaStar (1 / 18 : Real) →
            LT.lt.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (80 : Real) Erdos390.WholePaper.tangentSelbergCanonicalMainConstant) deltaStar) (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (u v : Nat),
                  LT.lt.{0} (0 : Nat) u →
                    LT.lt.{0} (0 : Nat) v →
                      LE.le.{0} v u →
                        LE.le.{0} u (Erdos390.Full.ArithmeticModel.yNat n) →
                          LE.le.{0} (HDiv.hDiv.{0, 0, 0} (α := Real) (↑u : Real) (↑v : Real)) r0 →
                            And (LE.le.{0} (HDiv.hDiv.{0, 0, 0} n v) (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentBroadUpper n K (Erdos390.WholePaper.upperTailLength c n)) u))
                              (LE.le.{0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0} (Erdos390.WholePaper.tangentEffectiveLowerCard (Erdos390.WholePaper.tangentPaperCleanListDensity W r0) n v)
                                      (Erdos390.WholePaper.tangentCanonicalExceptionalNatUpper n K (Erdos390.WholePaper.upperTailLength c n)
                                        (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) (Erdos390.Full.ArithmeticModel.yNat n) u v))
                                    (4 : Nat))
                                  (HMul.hMul.{0, 0, 0} (4 : Nat) (Erdos390.WholePaper.bankPaperSharpMarkerBudget n)))
                                (Erdos390.WholePaper.tangentRoughHeadCandidateLower W n K (Erdos390.WholePaper.upperTailLength c n) u v))

noncomputable def Erdos390.RemainingAnalyticGoal008_010 : Prop :=
∀ {c : Real},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    ∃ (depth : Nat),
      And (LE.le.{0} (201 : Nat) depth)
        (∀ (deltaStar : Real), Erdos390.WholePaper.IsPaperCombinedChargeDeltaStar c deltaStar → Erdos390.WholePaper.BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)

noncomputable def Erdos390.RemainingAnalyticGoal008_011 : Prop :=
∀ {c : Real},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    ∃ (depth : Nat),
      And (LE.le.{0} (201 : Nat) depth)
        (∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∃ (bank : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n))) (certificate :
            Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore bank)
              (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore bank) (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers bank depth)),
            And
              (Dvd.dvd.{0}
                (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.centralAnchorDivisor n (Erdos390.WholePaper.centralAnchorCutoff depth n) (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate))
                  (Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct bank))
                (Erdos390.WholePaper.centralTailProduct n (Erdos390.WholePaper.upperTailLength c n)))
              (And
                (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.WholePaper.primesUpTo (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat))) p →
                    LE.le.{0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0) (HMul.hMul.{0, 0, 0} (12 : Real) (↑(HSub.hSub.{0, 0, 0} p (1 : Nat)) : Real)))
                          (Erdos390.WholePaper.secondOrderScale n))
                        (↑(HAdd.hAdd.{0, 0, 0} (α := Nat) (β := Nat)
                              ((Nat.factorization
                                      (Erdos390.WholePaper.centralAnchorDivisor n (Erdos390.WholePaper.centralAnchorCutoff depth n)
                                        (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate)) :
                                    (a : Nat) → Nat)
                                  p :
                                Nat)
                              ((Nat.factorization (Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct bank) : (a : Nat) → Nat) p : Nat)) :
                          Real))
                      (↑(Erdos390.WholePaper.upperTailValuation c n p) : Real))
                (And
                  (∀ (p : Nat),
                    Membership.mem.{0, 0} (Erdos390.WholePaper.primesUpTo (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat))) p →
                      LE.le.{0}
                        (HAdd.hAdd.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0) (HMul.hMul.{0, 0, 0} (12 : Real) (↑(HSub.hSub.{0, 0, 0} p (1 : Nat)) : Real)))
                            (Erdos390.WholePaper.secondOrderScale n))
                          (↑((Nat.factorization (Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct bank) : (a : Nat) → Nat) p) : Real))
                        (↑((Nat.factorization (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) : (a : Nat) → Nat) p) : Real))
                  (And
                    (Dvd.dvd.{0} (Finset.prod.{0, 0} (Erdos390.WholePaper.baseBankFactors.{0} (Erdos390.WholePaper.BankPaperRealization.exactificationState bank)) id.{1})
                      (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate))
                    (Eq.{1}
                      (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate)
                        (Erdos390.WholePaper.centralAnchorDivisor n (Erdos390.WholePaper.centralAnchorCutoff depth n) (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate)))
                      (Erdos390.WholePaper.centralTailProduct n (Erdos390.WholePaper.upperTailLength c n)))))))

noncomputable def Erdos390.RemainingAnalyticGoal008_012 : Prop :=
∀ {c : Real}, LT.lt.{0} Erdos390.WholePaper.C0 c → ∃ (R : Nat), And (LE.le.{0} (201 : Nat) R) (∀ᶠ (n : Nat) in Filter.atTop.{0}, Nonempty.{1} (Erdos390.WholePaper.CentralAnchorCertificate c R n))

noncomputable def Erdos390.RemainingAnalyticGoal008_013 : Prop :=
∀ (W : Nat),
  ∃ (K : Real),
    And (LT.lt.{0} (0 : Real) K)
      (∃ (Y₀ : Nat),
        ∀ {X y d : Nat},
          LE.le.{0} Y₀ y →
            Membership.mem.{0, 0} (Nat.divisors (Erdos390.WholePaper.roughHeadModulus W)) d →
              LE.le.{0} d X →
                LE.le.{0} (Real.log (↑X : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0} (↑(Erdos390.Full.FriableAsymptotic.friableCount (HDiv.hDiv.{0, 0, 0} X d) y) : Real)
                        (HDiv.hDiv.{0, 0, 0} (α := Real) (↑(Erdos390.Full.FriableAsymptotic.friableCount X y) : Real) (↑d : Real))))
                    (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} K (↑X : Real)) (HMul.hMul.{0, 0, 0} (↑d : Real) (Real.log (↑y : Real)))) (3 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_014 : Prop :=
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ {n r y : Nat},
      LE.le.{0} (2 : Nat) n →
        LT.lt.{0} (0 : Nat) r →
          LE.le.{0} r n →
            LE.le.{0} (2 : Nat) y →
              LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
                LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.Scale.L n) (5 : Real)) (Real.log (↑y : Real)) →
                  LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n) : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) (↑n : Real)) (Erdos390.Full.Scale.L n)) →
                    LE.le.{0} (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n)) n →
                      LT.lt.{0} (0 : Nat) (Erdos390.WholePaper.upperTailLength c n) →
                        LE.le.{0}
                          (Erdos390.WholePaper.roughPhysicalDickmanTransitionLedger (Erdos390.WholePaper.roughHeadDensity W)
                            (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n)) beta
                            (Erdos390.Full.Scale.L n) (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) (Erdos390.WholePaper.upperTailLength c n)) r)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) r)
                            (HDiv.hDiv.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n))) r)
                            (HDiv.hDiv.{0, 0, 0} n r) y)
                          (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalSharpMainRowScaleConstant W K0 c beta)
                            (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(HDiv.hDiv.{0, 0, 0} n r) : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_015 : Prop :=
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ {n r y : Nat},
      LE.le.{0} (2 : Nat) n →
        LT.lt.{0} (0 : Nat) r →
          LE.le.{0} r n →
            LE.le.{0} (2 : Nat) y →
              LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
                LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.Scale.L n) (5 : Real)) (Real.log (↑y : Real)) →
                  LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n) : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) (↑n : Real)) (Erdos390.Full.Scale.L n)) →
                    LE.le.{0} (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n)) n →
                      LE.le.{0}
                        (Erdos390.WholePaper.roughPhysicalSaiasTransitionBudget (Erdos390.WholePaper.roughSaiasInvLogSqEndpointRate Erdos390.WholePaper.roughSaiasSharpDefectConstant)
                          (Erdos390.WholePaper.roughHeadDensity W)
                          (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n)) beta
                          (Erdos390.Full.Scale.L n) (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) (Erdos390.WholePaper.upperTailLength c n)) r)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) r)
                          (HDiv.hDiv.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) n) (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n))) r)
                          (HDiv.hDiv.{0, 0, 0} n r) y)
                        (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalSharpTransitionRowScaleConstant W K0 c beta)
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(HDiv.hDiv.{0, 0, 0} n r) : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_016 : Prop :=
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ {n y : Nat},
      LE.le.{0} (2 : Nat) n →
        LE.le.{0} (2 : Nat) y →
          ∀ (row : Erdos390.WholePaper.CanonicalCompleteRoughRow y (Erdos390.WholePaper.roughRawCandidateSet n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)))),
            LE.le.{0} (↑row : Nat) n →
              LE.le.{0} (1 : Real) (Erdos390.Full.Scale.L n) →
                LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Erdos390.Full.Scale.L n) (5 : Real)) (Real.log (↑y : Real)) →
                  LE.le.{0} (↑(Erdos390.WholePaper.upperTailLength c n) : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) c) (↑n : Real)) (Erdos390.Full.Scale.L n)) →
                    LE.le.{0} (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.upperTailLength c n)) n →
                      LE.le.{0}
                        (Erdos390.WholePaper.roughCanonicalSharpFixedHeadShiftBudgetAllRows W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) y
                          (Erdos390.WholePaper.roughHeadBalancedAlpha W n (Erdos390.WholePaper.upperTailLength c n) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) beta (Erdos390.Full.Scale.L n)) beta
                          (Erdos390.Full.Scale.L n) row)
                        (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughCanonicalSharpHeadRowScaleConstant W K0 c beta)
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(HDiv.hDiv.{0, 0, 0} n (↑row : Nat)) : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.Scale.L n) (2 : Nat))) (1 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_017 : Prop :=
∀ {A B y : Nat},
  LE.le.{0} (2 : Nat) y →
    LT.lt.{0} (0 : Nat) A →
      LE.le.{0} A B →
        LE.le.{0} (Real.log (↑B : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
          LE.le.{0} (HDiv.hDiv.{0, 0, 0} (2 : Real) (Real.log (↑y : Real))) Erdos390.WholePaper.roughCanonicalPoolDickmanFloor →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} Erdos390.WholePaper.roughCanonicalPoolDickmanFloor (2 : Real)) (↑(HSub.hSub.{0, 0, 0} B A) : Real))
              (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑B : Real) (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU B y)))
                (HMul.hMul.{0, 0, 0} (↑A : Real) (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU A y))))

noncomputable def Erdos390.RemainingAnalyticGoal008_018 : Prop :=
∀ {W : Nat} {Kshift : Real} {Y0 A B y : Nat},
  LT.lt.{0} (0 : Real) Kshift →
    (∀ {X z d : Nat},
        LE.le.{0} Y0 z →
          Membership.mem.{0, 0} (Nat.divisors (Erdos390.WholePaper.roughHeadModulus W)) d →
            LE.le.{0} d X →
              LE.le.{0} (Real.log (↑X : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑z : Real))) →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0} (↑(Erdos390.Full.FriableAsymptotic.friableCount (HDiv.hDiv.{0, 0, 0} X d) z) : Real)
                      (HDiv.hDiv.{0, 0, 0} (α := Real) (↑(Erdos390.Full.FriableAsymptotic.friableCount X z) : Real) (↑d : Real))))
                  (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Kshift (↑X : Real)) (HMul.hMul.{0, 0, 0} (↑d : Real) (Real.log (↑z : Real)))) (3 : Real))) →
      LE.le.{0} Y0 y →
        LE.le.{0} W y →
          LE.le.{0} (2 : Nat) y →
            LE.le.{0} (Erdos390.WholePaper.roughHeadModulus W) A →
              LE.le.{0} A B →
                LE.le.{0} (Real.log (↑B : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
                  LE.le.{0}
                    (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughHeadDensity W) (↑(Finset.card.{0} (Erdos390.Full.StructuredCells.smoothInterval A B y)) : Real))
                      (HMul.hMul.{0, 0, 0} (↑(Erdos390.WholePaper.roughHeadModulus W) : Real)
                        (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Kshift (HAdd.hAdd.{0, 0, 0} (α := Real) (↑A : Real) (↑B : Real))) (Real.log (↑y : Real))) (6 : Real))))
                    (↑(Finset.card.{0} (Erdos390.WholePaper.roughHeadFreeSmoothInterval W A B y)) : Real)

noncomputable def Erdos390.RemainingAnalyticGoal008_019 : Prop :=
∀ {f : Real → Real},
  LE.le.{0} (eVariationOn.{0, 0} f (Set.Icc.{0} (-5 : Real) (5 : Real))) (ENNReal.ofReal (2 : Real)) →
    ∀ {a b : Real},
      Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (5 : Real)) a →
        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (5 : Real)) b →
          LE.le.{0} a b →
            LE.le.{0} (∫ (v : Real) in (0 : Real)..(5 : Real), abs.{0} (HSub.hSub.{0, 0, 0} (f (HSub.hSub.{0, 0, 0} a v)) (f (HSub.hSub.{0, 0, 0} b v))))
              (HMul.hMul.{0, 0, 0} (2 : Real) (HSub.hSub.{0, 0, 0} b a))

noncomputable def Erdos390.RemainingAnalyticGoal008_020 : Prop :=
∀ {A B y d : Nat},
  LE.le.{0} (2 : Nat) y →
    LT.lt.{0} (0 : Nat) d →
      LE.le.{0} d A →
        LE.le.{0} A B →
          LE.le.{0} (Real.log (↑B : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
            LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect B y d) (Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect A y d)))
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} B A) : Real) (HAdd.hAdd.{0, 0, 0} (Real.log (↑d : Real)) (2 : Real)))
                (HMul.hMul.{0, 0, 0} (↑d : Real) (Real.log (↑y : Real))))

noncomputable def Erdos390.RemainingAnalyticGoal008_021 : Prop :=
Erdos390.WholePaper.RoughCompactBVTranslationPrinciple →
  ∀ {eta : Nat → Real} {Y₀ A B y d : Nat},
    Erdos390.WholePaper.RoughSaiasEndpointApproximationUpToFive eta Y₀ →
      LE.le.{0} Y₀ y →
        LE.le.{0} (2 : Nat) y →
          LT.lt.{0} (0 : Nat) d →
            LE.le.{0} d A →
              LE.le.{0} A B →
                LE.le.{0} (Real.log (↑B : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (HSub.hSub.{0, 0, 0} (α := Real) (↑(Erdos390.Full.FriableAsymptotic.friableCount (HDiv.hDiv.{0, 0, 0} B d) y) : Real)
                          (↑(Erdos390.Full.FriableAsymptotic.friableCount (HDiv.hDiv.{0, 0, 0} A d) y) : Real))
                        (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} (α := Real) (↑(Erdos390.Full.FriableAsymptotic.friableCount B y) : Real) (↑(Erdos390.Full.FriableAsymptotic.friableCount A y) : Real))
                          (↑d : Real))))
                    (Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget eta A B y d)

noncomputable def Erdos390.RemainingAnalyticGoal008_022 : Prop :=
∀ {ι : Type u_1} (I : Finset.{u_1} ι) (coeff : ι → Real) (endpoint : ι → Nat) (base y : Nat),
  (∀ (i : ι), Membership.mem.{u_1, u_1} I i → LE.le.{0} (Erdos390.Full.FriableAsymptotic.dickmanU (endpoint i) y) (5 : Real)) →
    LE.le.{0} (0 : Real) (Erdos390.Full.FriableAsymptotic.dickmanU base y) →
      LE.le.{0} (Erdos390.Full.FriableAsymptotic.dickmanU base y) (5 : Real) →
        LE.le.{0} (abs.{0} (∑ i ∈ I, HMul.hMul.{0, 0, 0} (coeff i) (Erdos390.WholePaper.roughFriableDickmanMain (endpoint i) y)))
          (HAdd.hAdd.{0, 0, 0} (α := Real)
            (∑ i ∈ I,
              HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (abs.{0} (coeff i)) (↑(endpoint i) : Real))
                (abs.{0} (HSub.hSub.{0, 0, 0} (Erdos390.Full.FriableAsymptotic.dickmanU (endpoint i) y) (Erdos390.Full.FriableAsymptotic.dickmanU base y))))
            (abs.{0} (∑ i ∈ I, HMul.hMul.{0, 0, 0} (coeff i) (↑(endpoint i) : Real))))

noncomputable def Erdos390.RemainingAnalyticGoal008_023 : Prop :=
∀ {X y d : Nat},
  LE.le.{0} (2 : Nat) y →
    LT.lt.{0} (0 : Nat) d →
      LE.le.{0} d X →
        LE.le.{0} (Real.log (↑X : Real)) (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log (↑y : Real))) →
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑(HDiv.hDiv.{0, 0, 0} X d) : Real) (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU (HDiv.hDiv.{0, 0, 0} X d) y)))
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑X : Real) (Erdos390.Full.DickmanBasic.rho (Erdos390.Full.FriableAsymptotic.dickmanU X y))) (↑d : Real))))
            (HAdd.hAdd.{0, 0, 0} (3 : Real) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑X : Real) (Real.log (↑d : Real))) (HMul.hMul.{0, 0, 0} (↑d : Real) (Real.log (↑y : Real)))))

noncomputable def Erdos390.RemainingAnalyticGoal008_024 : Prop :=
∀ {X a b : Nat},
  LE.le.{0} (2 : Nat) a →
    LE.le.{0} a b →
      LE.le.{0} b X →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
          LE.le.{0}
            (∑ m ∈ Finset.Ico.{0} a b,
              abs.{0}
                (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} X (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) (HAdd.hAdd.{0, 0, 0} m (1 : Nat)))
                  (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} X m) m)))
            (HDiv.hDiv.{0, 0, 0} (2 : Real) (Real.log (↑a : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_025 : Prop :=
∀ {q₁ q₀ m : Nat},
  LE.le.{0} (1 : Nat) q₁ →
    LE.le.{0} q₁ q₀ →
      LE.le.{0} (2 : Nat) m →
        LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑q₀ : Real)) (Real.log (↑m : Real))) (5 : Real) →
          Eq.{1} (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral q₁ (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral q₀ m))
            (∫ (t : Real) in (1 : Real)..HPow.hPow.{0, 0, 0} (α := Real) (↑m : Real) (5 : Real),
              HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (Int.fract.{0} t) (HPow.hPow.{0, 0, 0} t (2 : Nat)))
                (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasScaledDickmanKernel q₁ (HAdd.hAdd.{0, 0, 0} m (1 : Nat)) t) (Erdos390.WholePaper.roughSaiasScaledDickmanKernel q₀ m t)))

noncomputable def Erdos390.RemainingAnalyticGoal008_026 : Prop :=
Erdos390.WholePaper.RoughCompactBVTranslationPrinciple →
  ∀ {A B y : Nat},
    LT.lt.{0} (0 : Nat) A →
      LE.le.{0} A B →
        LE.le.{0} (2 : Nat) y →
          LE.le.{0} (Erdos390.Full.FriableAsymptotic.dickmanU B y) (5 : Real) →
            LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasDickmanCorrection B y) (Erdos390.WholePaper.roughSaiasDickmanCorrection A y)))
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (5 : Real) (↑(HSub.hSub.{0, 0, 0} B A) : Real)) (Real.log (↑y : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_027 : Prop :=
∀ {X a b m : Nat},
  LT.lt.{0} (0 : Nat) X →
    LE.le.{0} (2 : Nat) a →
      LE.le.{0} a b →
        LE.le.{0} b X →
          Membership.mem.{0, 0} (Finset.Ico.{0} a b) m →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
              ∀ {s : Real},
                Membership.mem.{0, 0} (γ := Set.{0} Real) (Set.Icc.{0} (↑m : Real) (↑(HAdd.hAdd.{0, 0, 0} m (1 : Nat)) : Real)) s →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} (↑X : Real) s) s)
                        (Erdos390.WholePaper.roughSaiasFullyRealBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} (α := Real) (↑X : Real) (↑(HAdd.hAdd.{0, 0, 0} m (1 : Nat)) : Real))
                          (↑(HAdd.hAdd.{0, 0, 0} m (1 : Nat)) : Real))))
                    (Erdos390.WholePaper.roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m)

noncomputable def Erdos390.RemainingAnalyticGoal008_028 : Prop :=
∀ {A B y d : Nat},
  LE.le.{0} (2 : Nat) y →
    LT.lt.{0} (0 : Nat) d →
      LE.le.{0} A B →
        LE.le.{0} (Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget (Erdos390.WholePaper.roughSaiasInvLogSqEndpointRate Erdos390.WholePaper.roughSaiasSharpDefectConstant) A B y d)
          (Erdos390.WholePaper.roughSaiasSharpIntervalFixedDivisorBudget A B y d)

noncomputable def Erdos390.RemainingAnalyticGoal008_029 : Prop :=
∀ {C : Real} {Y₀ : Nat},
  LE.le.{0} (0 : Real) C →
    Erdos390.WholePaper.RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀ →
      Erdos390.WholePaper.RoughSaiasEndpointApproximationUpToFive (Erdos390.WholePaper.roughSaiasInvLogSqEndpointRate C) (Erdos390.WholePaper.roughSaiasInvLogSqEndpointCutoff Y₀)

noncomputable def Erdos390.RemainingAnalyticGoal008_030 : Prop :=
∀ {X a b m : Nat},
  LE.le.{0} (2 : Nat) a →
    LE.le.{0} a b →
      LE.le.{0} b X →
        Membership.mem.{0, 0} (Finset.Ico.{0} a b) m →
          LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X m)))
              (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (16 : Real) (Erdos390.WholePaper.roughSaiasSelectorCellLedger X m))
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑X : Real) (HMul.hMul.{0, 0, 0} (↑m : Real) (Real.log (↑m : Real))))
                  (HAdd.hAdd.{0, 0, 0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.DickmanBasic.rho
                          (HDiv.hDiv.{0, 0, 0} (Real.log (↑(HDiv.hDiv.{0, 0, 0} X (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) : Real)) (Real.log (↑(HAdd.hAdd.{0, 0, 0} m (1 : Nat)) : Real))))
                        (Erdos390.Full.DickmanBasic.rho (HDiv.hDiv.{0, 0, 0} (Real.log (↑(HDiv.hDiv.{0, 0, 0} X m) : Real)) (Real.log (↑m : Real))))))
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} X (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) (HAdd.hAdd.{0, 0, 0} m (1 : Nat)))
                        (Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral (HDiv.hDiv.{0, 0, 0} X m) m))))))

noncomputable def Erdos390.RemainingAnalyticGoal008_031 : Prop :=
∀ {C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ {X M Z : Nat},
      LE.le.{0} (3 : Nat) M →
        LE.le.{0} M Z →
          LE.le.{0} Z X →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑M : Real))) (5 : Real) →
              LE.le.{0} X (HPow.hPow.{0, 0, 0} M (2 : Nat)) →
                LE.le.{0} (Erdos390.WholePaper.roughSaiasNaturalThetaPNTVariationLedger (4 : Real) C X M Z)
                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (13 : Real) C) (↑X : Real)) (HPow.hPow.{0, 0, 0} (Real.log (↑M : Real)) (2 : Nat)))

noncomputable def Erdos390.RemainingAnalyticGoal008_032 : Prop :=
∀ {X a c b : Nat},
  LE.le.{0} (2 : Nat) a →
    LE.le.{0} a c →
      LE.le.{0} c b →
        LE.le.{0} b X →
          ∀ {t : Real},
            LT.lt.{0} (0 : Real) t →
              (∀ (m : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} a c) m → LE.le.{0} t (HDiv.hDiv.{0, 0, 0} (α := Real) (↑(HDiv.hDiv.{0, 0, 0} X m) : Real) (↑m : Real))) →
                (∀ (m : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} a c) m → LE.le.{0} (Erdos390.WholePaper.roughSaiasBaseFreeDickmanCoordinate (HDiv.hDiv.{0, 0, 0} X m) m t) (5 : Real)) →
                  (∀ (m : Nat), Membership.mem.{0, 0} (Finset.Ioc.{0} c b) m → LT.lt.{0} (HDiv.hDiv.{0, 0, 0} (α := Real) (↑(HDiv.hDiv.{0, 0, 0} X m) : Real) (↑m : Real)) t) →
                    LE.le.{0}
                      (∑ m ∈ Finset.Ico.{0} a b,
                        abs.{0}
                          (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasScaledDickmanKernel (HDiv.hDiv.{0, 0, 0} X (HAdd.hAdd.{0, 0, 0} m (1 : Nat))) (HAdd.hAdd.{0, 0, 0} m (1 : Nat)) t)
                            (Erdos390.WholePaper.roughSaiasScaledDickmanKernel (HDiv.hDiv.{0, 0, 0} X m) m t)))
                      (HDiv.hDiv.{0, 0, 0} (2 : Real) (Real.log (↑a : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_033 : Prop :=
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  [inst_4 : Nonempty.{u_1 + 1} Head] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  {T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)} (candidates : Finset.{0} Nat) (preSelector : Nat → Real)
  (activeSeed : Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) → Real),
  Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstructor.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) T candidates preSelector activeSeed →
    (∀ (m : Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
        Eq.{1} (Erdos390.Full.PaperBridgeFit.BaselineAllocation.baseWeight.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B) m) (activeSeed m)) →
      ∀ (path : Real → Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) (label : Nat),
        Eq.{1} (α := Real)
          (∑
            a ∈
              Erdos390.WholePaper.completeRoughRowFiber
                (Erdos390.Full.ArithmeticModel.yNat (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) candidates label,
            Erdos390.WholePaper.bankPaperCanonicalActualP87EndpointSelector.{u_1, u_2} B candidates preSelector activeSeed path a)
          (∑
            a ∈
              Erdos390.WholePaper.completeRoughRowFiber
                (Erdos390.Full.ArithmeticModel.yNat (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) candidates label,
            preSelector a)

noncomputable def Erdos390.RemainingAnalyticGoal008_034 : Prop :=
∀ {X a b : Nat},
  LT.lt.{0} (0 : Nat) X →
    LE.le.{0} (2 : Nat) a →
      LE.le.{0} a b →
        LE.le.{0} b X →
          LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
            LE.le.{0} (∑ m ∈ Finset.Ico.{0} a b, Erdos390.WholePaper.roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) (HDiv.hDiv.{0, 0, 0} (2 : Real) (Real.log (↑a : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_035 : Prop :=
∀ {C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ {X a b : Nat},
      LE.le.{0} (2 : Nat) a →
        LE.le.{0} a b →
          LE.le.{0} b X →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
              LE.le.{0}
                (∑ m ∈ Finset.Ico.{0} a b,
                  HMul.hMul.{0, 0, 0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X (HAdd.hAdd.{0, 0, 0} m (1 : Nat)))
                        (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X m)))
                    (HMul.hMul.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} (↑m : Real) (HPow.hPow.{0, 0, 0} (Real.log (↑m : Real)) (4 : Nat)))))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (16 : Real)
                    (HAdd.hAdd.{0, 0, 0}
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (↑X : Real)) (HAdd.hAdd.{0, 0, 0} (2 : Real) (Real.log (↑b : Real))))
                        (HPow.hPow.{0, 0, 0} (Real.log (↑a : Real)) (5 : Nat)))
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (↑X : Real)) (HAdd.hAdd.{0, 0, 0} (1 : Real) (Real.log (↑b : Real))))
                        (HPow.hPow.{0, 0, 0} (Real.log (↑a : Real)) (6 : Nat)))))
                  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (↑X : Real)) (HPow.hPow.{0, 0, 0} (Real.log (↑a : Real)) (5 : Nat)))
                    (HAdd.hAdd.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} (2 : Real) (Real.log (↑a : Real))))))

noncomputable def Erdos390.RemainingAnalyticGoal008_036 : Prop :=
∀ {C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ {X a b : Nat},
      LE.le.{0} (3 : Nat) a →
        LE.le.{0} a b →
          LE.le.{0} b X →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (Real.log (↑X : Real)) (Real.log (↑a : Real))) (5 : Real) →
              LE.le.{0}
                (∑ m ∈ Finset.Ico.{0} a b,
                  HMul.hMul.{0, 0, 0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0} (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X (HAdd.hAdd.{0, 0, 0} m (1 : Nat)))
                        (Erdos390.WholePaper.roughSaiasNaturalQuotientThetaWeight X m)))
                    (HMul.hMul.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} (↑m : Real) (HPow.hPow.{0, 0, 0} (Real.log (↑m : Real)) (4 : Nat)))))
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (211 : Real) C) (↑X : Real)) (HPow.hPow.{0, 0, 0} (Real.log (↑a : Real)) (2 : Nat)))

noncomputable def Erdos390.RemainingAnalyticGoal008_037 : Prop :=
∀ {C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ (X : Nat) {M Z : Nat},
      LE.le.{0} (2 : Nat) M →
        LE.le.{0} M Z →
          LE.le.{0}
            (∑ m ∈ Finset.Ico.{0} M Z,
              HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughSaiasSelectorCellLedger X m)
                (HMul.hMul.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} (↑m : Real) (HPow.hPow.{0, 0, 0} (Real.log (↑m : Real)) (4 : Nat)))))
            (HAdd.hAdd.{0, 0, 0}
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (↑X : Real)) (HAdd.hAdd.{0, 0, 0} (2 : Real) (Real.log (↑Z : Real))))
                (HPow.hPow.{0, 0, 0} (Real.log (↑M : Real)) (5 : Nat)))
              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (↑X : Real)) (HAdd.hAdd.{0, 0, 0} (1 : Real) (Real.log (↑Z : Real))))
                (HPow.hPow.{0, 0, 0} (Real.log (↑M : Real)) (6 : Nat))))

noncomputable def Erdos390.RemainingAnalyticGoal008_038 : Prop :=
∀ {Request : Type u_1} [DecidableEq.{u_1 + 1} Request] (N : Nat) (source target lowerCard : Request → Nat) (disjointCharge : Real) (sharedCharge : Nat → Real),
  (∀ (request : Request), Ne.{1} (source request) (target request)) →
    (∀ (left right : Request) (leftSide rightSide : Erdos390.WholePaper.TangentEndpointSide),
        LE.le.{0}
          (HDiv.hDiv.{0, 0, 0}
            (↑(Erdos390.WholePaper.tangentEndpointEquationBudget N (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target leftSide left)
                  (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target rightSide right)) :
              Real)
            (HMul.hMul.{0, 0, 0} (α := Real) (↑(lowerCard left) : Real) (↑(lowerCard right) : Real)))
          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} disjointCharge (4 : Real))
            (ite.{1} (Eq.{1} (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target leftSide left) (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target rightSide right))
              (sharedCharge (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target leftSide left)) (0 : Real)))) →
      ∀ (left right : Request),
        LE.le.{0}
          (HDiv.hDiv.{0, 0, 0} (↑(Erdos390.WholePaper.tangentOrderedPairEndpointBudget.{u_1} N source target left right) : Real)
            (HMul.hMul.{0, 0, 0} (α := Real) (↑(lowerCard left) : Real) (↑(lowerCard right) : Real)))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} disjointCharge (ite.{1} (Erdos390.WholePaper.tangentRequestHasLabel.{u_1} source target (source left) right) (sharedCharge (source left)) (0 : Real)))
            (ite.{1} (Erdos390.WholePaper.tangentRequestHasLabel.{u_1} source target (target left) right) (sharedCharge (target left)) (0 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_039 : Prop :=
∀ {Request : Type u_1} [DecidableEq.{u_1 + 1} Request] (n K h labelUpper : Nat) (source target lowerCard : Request → Nat) (density : Real),
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Real) density →
      (∀ (request : Request), LT.lt.{0} (0 : Nat) (lowerCard request)) →
        (∀ (request : Request), Ne.{1} (source request) (target request)) →
          (∀ (request : Request) (side : Erdos390.WholePaper.TangentEndpointSide), Nat.Prime (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target side request)) →
            (∀ (request : Request) (side : Erdos390.WholePaper.TangentEndpointSide), LE.le.{0} (Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target side request) labelUpper) →
              LE.le.{0} (α := Real) (↑labelUpper : Real) (↑n : Real) →
                LE.le.{0} (HPow.hPow.{0, 0, 0} (α := Real) (↑labelUpper : Real) (2 : Nat)) (↑n : Real) →
                  (∀ (request : Request) (side : Erdos390.WholePaper.TangentEndpointSide),
                      LE.le.{0} (HMul.hMul.{0, 0, 0} density (↑n : Real))
                        (HMul.hMul.{0, 0, 0} (α := Real) (↑(lowerCard request) : Real) (↑(Erdos390.WholePaper.tangentEndpointLabel.{u_1} source target side request) : Real))) →
                    ∀ (left right : Request),
                      LE.le.{0}
                        (HDiv.hDiv.{0, 0, 0} (↑(Erdos390.WholePaper.tangentOrderedPairEndpointBudget.{u_1} (Erdos390.WholePaper.tangentBroadUpper n K h) source target left right) : Real)
                          (HMul.hMul.{0, 0, 0} (α := Real) (↑(lowerCard left) : Real) (↑(lowerCard right) : Real)))
                        (HAdd.hAdd.{0, 0, 0}
                          (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentDensityDisjointCoefficient density) (↑n : Real))
                            (ite.{1} (Erdos390.WholePaper.tangentRequestHasLabel.{u_1} source target (source left) right)
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.tangentDensitySharedCoefficient density) (↑(source left) : Real)) (↑n : Real)) (0 : Real)))
                          (ite.{1} (Erdos390.WholePaper.tangentRequestHasLabel.{u_1} source target (target left) right)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.tangentDensitySharedCoefficient density) (↑(target left) : Real)) (↑n : Real)) (0 : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal008_040 : Prop :=
∀ {W n K h u v : Nat} {r0 : Real},
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Nat) u →
      LT.lt.{0} (0 : Nat) v →
        LT.lt.{0} (1 : Real) r0 →
          LT.lt.{0} r0 (2 : Real) →
            LE.le.{0} (HDiv.hDiv.{0, 0, 0} (α := Real) (↑u : Real) (↑v : Real)) r0 →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.roughHeadDensity W) (HDiv.hDiv.{0, 0, 0} (α := Real) (↑(HMul.hMul.{0, 0, 0} K h) : Real) (↑n : Real)))
                  (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (16 : Real)) →
                LE.le.{0}
                    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (α := Real) (↑u : Real) (↑n : Real))
                      (HAdd.hAdd.{0, 0, 0} (Erdos390.WholePaper.roughHeadDensity W) (↑(Erdos390.WholePaper.roughHeadModulus W) : Real)))
                    (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (16 : Real)) →
                  And (LE.le.{0} (HDiv.hDiv.{0, 0, 0} n v) (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentBroadUpper n K h) u))
                    (LE.le.{0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) (Erdos390.WholePaper.tangentPaperHeadGap W r0)) (4 : Real))
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (α := Real) (↑u : Real) (↑n : Real)) (Erdos390.WholePaper.tangentRoughHeadCandidateMain W n K h u v)))


