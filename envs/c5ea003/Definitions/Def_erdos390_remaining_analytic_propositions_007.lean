-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_007
-- name    : erdos390_remaining_analytic_propositions_007
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:43:17.504199+00:00
-- url     : https://prove2.me/theorems/675ae4d3-e0d7-4b2f-8364-d829efe3acd2
-- title:
--   Analytic construction propositions, part 7
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates, exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate, exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual, exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate, exists_uniform_guardedRawCell_valuation_mean_profiles_paperRate, exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate, exists_uniform_movingPrefix_density_lower_bound_of_fraction, exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction, exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction, exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate, exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate, exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate, exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate.
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
universe u_1
set_option maxRecDepth 10000
set_option maxHeartbeats 0


noncomputable def Erdos390.RemainingAnalyticGoal007_001 : Prop :=
∀ {c : Real} {depth n W K h X0 : Nat} (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (fixedExceptional fixed candidates : Finset.{0} Nat) (selector : Nat → Real) {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band] (lastCell : Band → Nat)
  (bandOf : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Band) (cellIndex : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Nat)
  (pointwiseUpper : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real) (prefixUpper : Band → Nat → Real),
  Erdos390.WholePaper.BankPaperCanonicalRoundedSelectorTangentInput.{u_1} R certificate fixed candidates bandOf cellIndex pointwiseUpper prefixUpper selector →
    ∀ (density L sigma N trafficConstant incidentConstant tangentConstant width trafficError incidentError weightedResidual weightedPort : Real),
      LT.lt.{0} (0 : Nat) n →
        LT.lt.{0} (0 : Real) density →
          LT.lt.{0} (0 : Real) L →
            LT.lt.{0} (0 : Real) sigma →
              LT.lt.{0} (0 : Real) N →
                Eq.{1} (HMul.hMul.{0, 0, 0} L N) (↑n : Real) →
                  (∀ (a : Nat), Membership.mem.{0, 0} fixed a → LT.lt.{0} (0 : Nat) a) →
                    Dvd.dvd.{0} (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R fixed) (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) →
                      (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W), LE.le.{0} (cellIndex p) (lastCell (bandOf p))) →
                        (∀ (band : Band) (cell : Nat), LE.le.{0} cell (lastCell band) → Ne.{1} (Erdos390.WholePaper.tangentRatioCellCard.{0, u_1} bandOf cellIndex band cell) (0 : Nat)) →
                          (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
                              LE.le.{0}
                                (HMul.hMul.{0, 0, 0} (↑(Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel p) : Real)
                                  (abs.{0} (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector p)))
                                weightedResidual) →
                            (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
                                LE.le.{0}
                                  (HMul.hMul.{0, 0, 0} (↑(Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel p) : Real)
                                    (Erdos390.WholePaper.tangentRatioCellUniformPortLoad.{0, u_1} (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf
                                      cellIndex p))
                                  weightedPort) →
                              LE.le.{0}
                                  (Erdos390.WholePaper.tangentDistributedTotalTrafficLedger.{0} (V := Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                    (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector)
                                    (Erdos390.WholePaper.tangentRatioCellCanonicalCutTraffic.{0, u_1} lastCell
                                      (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} trafficConstant tangentConstant) N) width) (HMul.hMul.{0, 0, 0} trafficError N)) →
                                LE.le.{0} (HAdd.hAdd.{0, 0, 0} weightedResidual (HMul.hMul.{0, 0, 0} (2 : Real) weightedPort))
                                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} incidentConstant tangentConstant) N) width)
                                      (HMul.hMul.{0, 0, 0} incidentError N)) →
                                  LE.le.{0} (Erdos390.WholePaper.tangentDistributedPaperMainBudget trafficConstant incidentConstant tangentConstant width sigma)
                                      (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (48 : Real)) →
                                    LE.le.{0} (Erdos390.WholePaper.tangentDistributedPaperErrorBudget trafficError incidentError sigma)
                                        (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (96 : Real)) →
                                      LE.le.{0}
                                          (Erdos390.WholePaper.tangentDistributedPaperCeilingBudget n (Erdos390.Full.ArithmeticModel.yNat n)
                                            (Erdos390.WholePaper.tangentDistributedSupportCount.{0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)))
                                          (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} density (2 : Nat)) (96 : Real)) →
                                        (∀
                                            (request :
                                              Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                  (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                L sigma),
                                            LT.lt.{0} (0 : Nat) (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (density := density) request)) →
                                          (∀
                                              (request :
                                                Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                  (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                    (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                  L sigma),
                                              LE.le.{0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (density := density) request)
                                                (Finset.card.{0}
                                                  (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                                                    (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                      (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                        (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                    (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                                                    (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
                                                    (fun (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                      Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                        (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2)
                                                    n K h (Erdos390.WholePaper.roughHeadModulus W) X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                    (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                    (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request))) →
                                            (∀
                                                (request :
                                                  Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                    (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                      (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                    L sigma)
                                                (side : Erdos390.WholePaper.TangentEndpointSide),
                                                LE.le.{0} (HMul.hMul.{0, 0, 0} density (↑n : Real))
                                                  (HMul.hMul.{0, 0, 0} (α := Real) (↑(Erdos390.WholePaper.bankPaperCanonicalDistributedTangentLowerCard (density := density) request) : Real)
                                                    (↑(Erdos390.WholePaper.tangentEndpointLabel.{0} Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource
                                                          Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget side request) :
                                                      Real))) →
                                              (∀
                                                  (request :
                                                    Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                      (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                        (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                      L sigma)
                                                  {common : Nat},
                                                  Membership.mem.{0, 0}
                                                      (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                                                        (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                          (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                            (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                        (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                                                        (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
                                                        (fun (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                          Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                            (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2)
                                                        n K h (Erdos390.WholePaper.roughHeadModulus W) X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                        (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                        (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request)
                                                      common →
                                                    And (Membership.mem.{0, 0} candidates (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) common))
                                                      (Membership.mem.{0, 0} candidates (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) common))) →
                                                (∀
                                                    (request :
                                                      Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                        (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                          (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                        L sigma)
                                                    (multiplier : Nat),
                                                    Membership.mem.{0, 0}
                                                        (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                                                          (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                            (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                          (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                                                          (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
                                                          (fun (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                            Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2)
                                                          n K h (Erdos390.WholePaper.roughHeadModulus W) X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                          (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                          (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request)
                                                        multiplier →
                                                      And
                                                        (And
                                                          (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                                            (selector (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) multiplier)))
                                                          (LE.le.{0} (selector (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) multiplier))
                                                            (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L))))
                                                        (And
                                                          (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                                            (selector (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) multiplier)))
                                                          (LE.le.{0} (selector (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) multiplier))
                                                            (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L))))) →
                                                  ∃ (multiplier :
                                                    Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                        (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                          (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                        L sigma →
                                                      Nat),
                                                    And
                                                      (∀
                                                        (request :
                                                          Erdos390.WholePaper.TangentSplitRequest.{0}
                                                            (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                              (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                            L sigma
                                                            fun
                                                              (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                            Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2),
                                                        Membership.mem.{0, 0}
                                                          (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                                                            (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                              (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                            (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                                                            (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
                                                            (fun
                                                                (edge :
                                                                  Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                              Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2)
                                                            n K h (Erdos390.WholePaper.roughHeadModulus W) X0 (Erdos390.Full.ArithmeticModel.yNat n)
                                                            (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                                                            (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate fixedExceptional) request)
                                                          (multiplier request))
                                                      (And
                                                        (Erdos390.WholePaper.TangentEndpointsDistinct.{0}
                                                          (Erdos390.WholePaper.tangentSplitRequests.{0}
                                                            (Erdos390.WholePaper.tangentPositiveFlowEdges.{0}
                                                              (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex))
                                                            L sigma
                                                            fun
                                                              (edge : Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W) (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                                            Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex edge.1 edge.2)
                                                          Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget
                                                          multiplier)
                                                        (And
                                                          (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
                                                            Eq.{1}
                                                              (Erdos390.WholePaper.tangentFlowDivergence.{0}
                                                                (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                  (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                                p)
                                                              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector p))
                                                          (And
                                                            (∀ (q : Nat),
                                                              Eq.{1}
                                                                (∑ request :
                                                                  Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest
                                                                    (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                      (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                                    L sigma,
                                                                  HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.tangentSplitRequestWeight.{0} request)
                                                                    (HSub.hSub.{0, 0, 0} (α := Real)
                                                                      (↑((Nat.factorization (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) : (a : Nat) → Nat) q) :
                                                                        Real)
                                                                      (↑((Nat.factorization (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) : (a : Nat) → Nat) q) :
                                                                        Real)))
                                                                (Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates selector q))
                                                            (∃ (output : Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput R certificate candidates fixed),
                                                              Eq.{1} (Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput.selector output)
                                                                (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentUpdatedSelector
                                                                  (Erdos390.WholePaper.tangentRatioCellEarthmoverFlow.{0, u_1} lastCell
                                                                    (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector) bandOf cellIndex)
                                                                  L sigma multiplier selector)))))

noncomputable def Erdos390.RemainingAnalyticGoal007_002 : Prop :=
∀ (Phead : Finset.{0} Nat) (Patterns : Erdos390.Full.PaperHeadSimplex.Tag Phead → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W K0 depth : Nat),
  LE.le.{0} (2 : Nat) W →
    (∀ (h : Erdos390.Full.PaperHeadSimplex.Tag Phead) (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Patterns h)) q → LE.le.{0} q W) →
      ∀ {c deltaStar betaProt betaAct epsilon cMass Azero Cd : Real},
        LT.lt.{0} (0 : Real) c →
          LT.lt.{0} (0 : Real) deltaStar →
            LT.lt.{0} deltaStar (1 / 18 : Real) →
              LT.lt.{0} (0 : Real) epsilon →
                LT.lt.{0} (0 : Real) cMass →
                  LE.le.{0} (0 : Real) Azero →
                    LE.le.{0} (0 : Real) Cd →
                      LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
                        ∃ (Cinitial : Real),
                          And (LE.le.{0} (0 : Real) Cinitial)
                            (∀ᶠ (n : Nat) in Filter.atTop.{0},
                              ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hmesh : LT.lt.{0} (0 : Real) delta)
                                (Bsource : Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag Phead) (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)),
                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource)) n →
                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource)) W →
                                    ∀
                                      (R :
                                        Erdos390.WholePaper.BankPaperRealization
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource))
                                          (Erdos390.WholePaper.upperEndpoint
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource))
                                            (Erdos390.WholePaper.upperTailLength c
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource)))))
                                      (certificate :
                                        Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} Bsource))
                                          (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                          (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                      (J : Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt M Bsource (K0 := K0) R certificate I deltaStar hmesh)
                                      (_S : Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt M Bsource R certificate I deltaStar hmesh J),
                                      Eq.{1} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt J) betaProt →
                                        Eq.{1} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct J) betaAct →
                                          ∀
                                            (hsep :
                                              LT.lt.{0}
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))))
                                            (hremaining :
                                              ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag Phead)),
                                                Finset.Nonempty.{0}
                                                  (SDiff.sdiff.{0}
                                                    (Erdos390.Full.PaperGuardCensus.rawCell.{0} Patterns I
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                          (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                      cell)
                                                    (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                          (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                      (G
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))))),
                                            Eq.{1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                  (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))
                                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} Patterns I (W :=
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                  (G
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                  hsep hremaining) →
                                              Eq.{1} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde J)
                                                  (Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                    (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct J)) →
                                                And (LE.le.{0} (0 : Real) (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha J))
                                                    (LE.le.{0} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha J) (1 : Real)) →
                                                  And
                                                      (LE.le.{0} (0 : Real)
                                                        (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta J)
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                      (LE.le.{0}
                                                        (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta J)
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                        (1 : Real)) →
                                                    Finset.Nonempty.{0}
                                                        (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                              (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                          (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat)) →
                                                      LE.le.{0} (abs.{0} (↑(Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d J) : Real))
                                                          (HMul.hMul.{0, 0, 0} Cd
                                                            (HDiv.hDiv.{0, 0, 0}
                                                              (Erdos390.WholePaper.secondOrderScale
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0}
                                                                (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))) →
                                                        LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} cMass
                                                              (Erdos390.WholePaper.secondOrderScale
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))))
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.q.{0, 0}
                                                              (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)) →
                                                          (∀
                                                              (p :
                                                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                              (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              LE.le.{0}
                                                                (Erdos390.Full.FiniteProbability.expect.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)
                                                                    (Prod.mk.{0, 0} Option.none.{0} sigma))
                                                                  fun
                                                                    (m :
                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0}
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                          (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))
                                                                        (Prod.mk.{0, 0} Option.none.{0} sigma)) =>
                                                                  Erdos390.Full.ArithmeticModel.valuation (↑p : Nat) (↑m : Nat))
                                                                (HDiv.hDiv.{0, 0, 0} Azero (↑(↑p : Nat) : Real))) →
                                                            ∀ (p : Nat),
                                                              Membership.mem.{0, 0}
                                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J))))
                                                                  p →
                                                                LE.le.{0}
                                                                  (abs.{0}
                                                                    (Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit R certificate
                                                                      (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar)
                                                                      (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet R certificate deltaStar
                                                                        (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)))
                                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector J) p))
                                                                  (HDiv.hDiv.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} Cinitial
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.q.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))
                                                                    (HMul.hMul.{0, 0, 0} (↑p : Real)
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge J)))))

noncomputable def Erdos390.RemainingAnalyticGoal007_003 : Prop :=
∀ (P : Finset.{0} Nat) (hprime : ∀ (p : Nat), @Membership.mem.{0, 0} Nat (Finset.{0} Nat) _ P p → Nat.Prime p) (E : Nat),
  @LT.lt.{0} Nat _ (@OfNat.ofNat.{0} Nat (nat_lit 0) _) E →
    ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals),
      (∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 1) _) (I.lower sign)) →
        (∀ (sign : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LT.lt.{0} Real _ (I.upper sign) (@OfNat.ofNat.{0} Real (nat_lit 2) _)) →
          ∀ {c : Real} (depth W K0 Ntail : Nat) (F : Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily c depth Ntail) {deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor : Real},
            @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) c →
              @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) betaAct →
                @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) mu →
                  @LE.le.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) betaProt →
                    @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) sourceMarginFloor →
                      @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) headMarginFloor →
                        @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) physicalEtaFloor →
                          @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) postMarginFloor →
                            @HasSubset.Subset.{0} (Finset.{0} Nat) _ (Erdos390.WholePaper.primesUpTo W) P →
                              ∀ (logY Lambda0 mFrozen : Nat → Real),
                                Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedger (fun (n : Nat) => Erdos390.WholePaper.bankPaperCanonicalRawSmoothBaseMass W n (Erdos390.WholePaper.upperTailLength c n) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass c depth Ntail F W (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct deltaStar) (Erdos390.WholePaper.bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass c depth Ntail F W (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct deltaStar)) →
                                  @Exists.{1} Real fun (Cmass : Real) =>
                                    @Exists.{1} Real fun (density : Real) =>
                                      And (@LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) Cmass)
                                        (And (@LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) density)
                                          (∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta),
                                            @Filter.Eventually.{0} Nat
                                              (fun (n : Nat) =>
                                                ∀ (hdelta : @LT.lt.{0} Real _ (@OfNat.ofNat.{0} Real (nat_lit 0) _) delta) (Bsource : @Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _),
                                                  @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) n →
                                                    @Eq.{1} Nat (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) W →
                                                      ∀ (hnTail : @LE.le.{0} Nat _ Ntail (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))),
                                                        let R := @Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail;
                                                        let certificate := @Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail;
                                                        ∀ (J : @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta), @Eq.{1} Nat (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) E → @Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) betaProt → @Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) betaAct → ∀ (hsep : @LT.lt.{0} Nat _ (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))) (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))) (hremaining : ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)), @Finset.Nonempty.{0} Nat (@SDiff.sdiff.{0} (Finset.{0} Nat) _ (@Erdos390.Full.PaperGuardCensus.rawCell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) cell) (@Erdos390.Full.PaperGuardCensus.Ledger.guards (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (@OfNat.ofNat.{0} Nat (nat_lit 2) _) (@OfNat.ofNat.{0} Nat (nat_lit 0) _) (Erdos390.WholePaper.roughCanonicalBridgeRelevantLedgerFamily depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))))))), @Eq.{1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _) (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (Erdos390.Full.PaperHeadSimplex.pattern P hprime E) I (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (@OfNat.ofNat.{0} Nat (nat_lit 2) _) (@OfNat.ofNat.{0} Nat (nat_lit 0) _) (Erdos390.WholePaper.roughCanonicalBridgeRelevantLedgerFamily depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))) hsep hremaining) → @Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail) depth) R certificate deltaStar (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @LE.le.{0} Real _ sourceMarginFloor (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @LE.le.{0} Real _ headMarginFloor (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.headMargin.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ Bsource I (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) Bsource c depth R certificate deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource c K0 (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) Bsource c depth R certificate (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource c K0 (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@HAdd.hAdd.{0, 0, 0} Real Real Real _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ Bsource c depth R certificate deltaStar) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @LE.le.{0} Real _ physicalEtaFloor (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.physicalEta.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ Bsource I (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) Bsource c depth R certificate deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource c K0 (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) Bsource c depth R certificate (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource c K0 (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@HAdd.hAdd.{0, 0, 0} Real Real Real _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ Bsource c depth R certificate deltaStar) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @LE.le.{0} Real _ postMarginFloor (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightTarget delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @Eq.{1} Real (mFrozen (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))) (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenSmoothFrozenMass.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) c depth (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) R certificate deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)) → @Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (Erdos390.WholePaper.bankPaperCanonicalSmoothFinalActiveMassFamily mu logY Lambda0 mFrozen (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass c depth Ntail F W (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct deltaStar) (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))) → @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt.{0} P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) c depth (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) R certificate (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))) R deltaStar) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) deltaStar (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) → And (@Dvd.dvd.{0} Nat _ (@HMul.hMul.{0, 0, 0} Nat Nat Nat _ (Erdos390.WholePaper.centralAnchorDivisor (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (Erdos390.WholePaper.centralAnchorCutoff depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))) (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.q c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail) depth) certificate)) (@Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) R)) (Erdos390.WholePaper.centralTailProduct (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J))) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J)))))) (@Dvd.dvd.{0} Nat _ (@Erdos390.WholePaper.BankPaperRealization.selectorTailCharge (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) R (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource))) R deltaStar)) (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget c depth (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail)) (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperEndpoint (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) (Erdos390.WholePaper.upperTailLength c (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)))) (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization c depth Ntail F (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P) _ (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M) _ _ _ _ Bsource)) hnTail) depth) certificate)) → @Exists.{1} (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) fun (S : @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J) => @Exists.{0} (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt delta eta M P Bsource c depth K0 R certificate I E deltaStar mu sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor logY Lambda0 mFrozen (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass c depth Ntail F W (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct deltaStar) hdelta J S) fun (_Hgap : @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt delta eta M P Bsource c depth K0 R certificate I E deltaStar mu sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor logY Lambda0 mFrozen (@Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass c depth Ntail F W (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat _ K0 (@OfNat.ofNat.{0} Nat (nat_lit 1) _)) betaAct deltaStar) hdelta J S) => And (@Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt.Cmass delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J S) Cmass) (@Eq.{1} Real (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightSourceInputsAt.density delta eta M P Bsource c depth K0 R certificate I deltaStar hdelta J S) density))
                                              (@Filter.atTop.{0} Nat _)))

noncomputable def Erdos390.RemainingAnalyticGoal007_004 : Prop :=
∀ {P : Finset.{0} Nat} (Patterns : Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
  LT.lt.{0} (1 : Nat) W →
    (∀ (h : Erdos390.Full.PaperHeadSimplex.Tag P) (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Patterns h)) q → LE.le.{0} q W) →
      ∃ (Azero : Real),
        And (LT.lt.{0} (0 : Real) Azero)
          (∃ (N₀ : Nat),
            ∀ {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band] (B : Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band),
              LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) →
                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) W →
                  ∀
                    (hsep :
                      LT.lt.{0}
                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
                    (hremaining :
                      ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
                        Finset.Nonempty.{0}
                          (SDiff.sdiff.{0}
                            (Erdos390.Full.PaperGuardCensus.rawCell.{0} Patterns I
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) cell)
                            (Erdos390.Full.PaperGuardCensus.Ledger.guards (n := Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                              (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))))),
                    Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} Patterns I (W :=
                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                          (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))) hsep hremaining) →
                      ∀
                        (p :
                          Erdos390.Full.ArithmeticBandGeometry.BandPrime (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                        (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                        LE.le.{0}
                          (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{0, u_1} B (Prod.mk.{0, 0} Option.none.{0} sigma))
                            fun
                              (m :
                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                                  (Prod.mk.{0, 0} Option.none.{0} sigma)) =>
                            Erdos390.Full.ArithmeticModel.valuation (↑p : Nat) (↑m : Nat))
                          (HDiv.hDiv.{0, 0, 0} Azero (↑(↑p : Nat) : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal007_005 : Prop :=
∀ {Head : Type u_1} [Fintype.{u_1} Head] [Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W : Nat),
  LT.lt.{0} (1 : Nat) W →
    (∀ (h : Head) (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (P h)) q → LE.le.{0} q W) →
      ∃ (Cval : Real),
        And (LT.lt.{0} (0 : Real) Cval)
          (∃ (N₀ : Nat),
            ∀ {n p : Nat},
              LE.le.{0} N₀ n →
                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                  have Kcut := Nat.log p (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat));
                  ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                    (hremaining : Finset.Nonempty.{0} (SDiff.sdiff.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I n c) (Erdos390.Full.PaperGuardCensus.Ledger.guards (G n)))),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.expect.{0}
                            (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                              (SDiff.sdiff.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I n c) (Erdos390.Full.PaperGuardCensus.Ledger.guards (G n))) hremaining)
                            fun (m : ↥(SDiff.sdiff.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P I n c) (Erdos390.Full.PaperGuardCensus.Ledger.guards (G n)))) =>
                            Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                          (∑ k ∈ Erdos390.Full.ArithmeticModel.positiveExponents Kcut, Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p k))))
                      (HDiv.hDiv.{0, 0, 0} Cval (HMul.hMul.{0, 0, 0} (↑p : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_006 : Prop :=
∀ (W K depth : Nat),
  LT.lt.{0} (1 : Nat) W →
    ∀ {c : Real},
      LT.lt.{0} (0 : Real) c →
        ∃ (Cval : Real),
          And (LT.lt.{0} (0 : Real) Cval)
            (∃ (N₀ : Nat),
              ∀ {n p : Nat} (R : Erdos390.WholePaper.BankPaperRealization n (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
                (certificate :
                  Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
                    (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R) (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                (deltaStar : Real),
                LE.le.{0} N₀ n →
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    ∀ (hguarded : Finset.Nonempty.{0} (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K (1 : Nat))),
                      have Kcut := Nat.log p (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat));
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.expect.{0}
                              (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                                (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K (1 : Nat)) hguarded)
                              fun (m : ↥(Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K (1 : Nat))) =>
                              Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                            (∑ j ∈ Erdos390.Full.ArithmeticModel.positiveExponents Kcut, Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p j))))
                        (HDiv.hDiv.{0, 0, 0} Cval (HMul.hMul.{0, 0, 0} (↑p : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_007 : Prop :=
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C rmin : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        LT.lt.{0} (0 : Real) rmin →
          ∃ (cprefix : Real),
            And (LT.lt.{0} (0 : Real) cprefix)
              (∃ (N₀ : Nat),
                ∀ {n k : Nat},
                  LE.le.{0} N₀ n →
                    LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                      LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                        LE.le.{0} rmin (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixFraction A C n k) →
                          And (LT.lt.{0} (0 : Nat) (Erdos390.Full.ArithmeticModel.physicalBound C n))
                            (LE.le.{0} (HMul.hMul.{0, 0, 0} cprefix (↑(Erdos390.Full.ArithmeticModel.physicalBound C n) : Real))
                              (↑(Finset.card.{0} (Erdos390.Full.StructuredCells.structuredCell P (Erdos390.Full.ArithmeticModel.physicalBound A n) k (Erdos390.Full.ArithmeticModel.yNat n))) : Real)))

noncomputable def Erdos390.RemainingAnalyticGoal007_008 : Prop :=
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C rmin : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) rmin →
        ∃ (K : Real),
          And (LT.lt.{0} (0 : Real) K)
            (∃ (N₀ : Nat),
              ∀ {n k d : Nat},
                LE.le.{0} N₀ n →
                  LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                    LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                      LE.le.{0} rmin (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixFraction A C n k) →
                        LT.lt.{0} (0 : Nat) d →
                          LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                            Membership.mem.{0, 0} (Nat.smoothNumbers (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (1 : Nat))) d →
                              Nat.Coprime d (Erdos390.Full.HeadPattern.Pattern.modulus P) →
                                have S := Erdos390.Full.StructuredCells.structuredCell P (Erdos390.Full.ArithmeticModel.physicalBound A n) k (Erdos390.Full.ArithmeticModel.yNat n);
                                ∃ (_ : Finset.Nonempty.{0} S),
                                  LE.le.{0}
                                    (abs.{0}
                                      (HSub.hSub.{0, 0, 0} (Erdos390.Full.DivisibilityMomentBounds.uniformAverage S (Erdos390.Full.ArithmeticModel.divInd d))
                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n d)))
                                    (HDiv.hDiv.{0, 0, 0} K (HMul.hMul.{0, 0, 0} (↑d : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_009 : Prop :=
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C rmin : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        LT.lt.{0} (0 : Real) rmin →
          ∀ (W : Nat),
            LT.lt.{0} (1 : Nat) W →
              (∀ (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes P) q → LE.le.{0} q W) →
                ∃ (Cval : Real),
                  And (LT.lt.{0} (0 : Real) Cval)
                    (∃ (N₀ : Nat),
                      ∀ {n k p : Nat},
                        LE.le.{0} N₀ n →
                          LT.lt.{0} (Erdos390.Full.ArithmeticModel.physicalBound A n) k →
                            LE.le.{0} k (Erdos390.Full.ArithmeticModel.physicalBound C n) →
                              LE.le.{0} rmin (Erdos390.Full.PaperMovingPrefixMarkedCell.prefixFraction A C n k) →
                                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                                  have S := Erdos390.Full.StructuredCells.structuredCell P (Erdos390.Full.ArithmeticModel.physicalBound A n) k (Erdos390.Full.ArithmeticModel.yNat n);
                                  have Kcut := Nat.log p (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat));
                                  ∃ (hS : Finset.Nonempty.{0} S),
                                    LE.le.{0}
                                      (abs.{0}
                                        (HSub.hSub.{0, 0, 0}
                                          (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun (m : ↥S) =>
                                            Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                                          (∑ j ∈ Erdos390.Full.ArithmeticModel.positiveExponents Kcut, Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p j))))
                                      (HDiv.hDiv.{0, 0, 0} Cval (HMul.hMul.{0, 0, 0} (↑p : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_010 : Prop :=
∀ (W K : Nat),
  LT.lt.{0} (1 : Nat) W →
    ∀ {c : Real},
      LT.lt.{0} (0 : Real) c →
        ∃ (Cval : Real),
          And (LT.lt.{0} (0 : Real) Cval)
            (∃ (N₀ : Nat),
              ∀ {n p : Nat},
                LE.le.{0} N₀ n →
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    have S := Erdos390.WholePaper.bankPaperCanonicalRawSmoothBasePool W n (Erdos390.WholePaper.upperTailLength c n) K;
                    have Kcut := Nat.log p (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat));
                    ∃ (hS : Finset.Nonempty.{0} S),
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun (m : ↥S) => Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                            (∑ j ∈ Erdos390.Full.ArithmeticModel.positiveExponents Kcut, Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p j))))
                        (HDiv.hDiv.{0, 0, 0} Cval (HMul.hMul.{0, 0, 0} (↑p : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_011 : Prop :=
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A C : Real},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} A C →
      LT.lt.{0} (0 : Real) C →
        ∀ (W : Nat),
          LT.lt.{0} (1 : Nat) W →
            (∀ (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes P) q → LE.le.{0} q W) →
              ∃ (Cval : Real),
                And (LT.lt.{0} (0 : Real) Cval)
                  (∃ (N₀ : Nat),
                    ∀ {n p : Nat},
                      LE.le.{0} N₀ n →
                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                          have S :=
                            Erdos390.Full.StructuredCells.structuredCell P (Erdos390.Full.ArithmeticModel.physicalBound A n) (Erdos390.Full.ArithmeticModel.physicalBound C n)
                              (Erdos390.Full.ArithmeticModel.yNat n);
                          have Kcut := Nat.log p (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat));
                          ∃ (hS : Finset.Nonempty.{0} S),
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (Erdos390.Full.FiniteProbability.expect.{0} (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) fun (m : ↥S) =>
                                    Erdos390.Full.ArithmeticModel.valuation p (↑m : Nat))
                                  (∑ k ∈ Erdos390.Full.ArithmeticModel.positiveExponents Kcut, Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n (HPow.hPow.{0, 0, 0} p k))))
                              (HDiv.hDiv.{0, 0, 0} Cval (HMul.hMul.{0, 0, 0} (↑p : Real) (Erdos390.Full.Scale.L n))))

noncomputable def Erdos390.RemainingAnalyticGoal007_012 : Prop :=
∀ (Phead : Finset.{0} Nat) (Patterns : Erdos390.Full.PaperHeadSimplex.Tag Phead → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W K0 depth : Nat),
  LT.lt.{0} (1 : Nat) W →
    (∀ (h : Erdos390.Full.PaperHeadSimplex.Tag Phead) (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Patterns h)) q → LE.le.{0} q W) →
      ∀ {c : Real},
        LT.lt.{0} (0 : Real) c →
          ∀ (betaAct Azero Cd : Real),
            LE.le.{0} (0 : Real) Azero →
              LE.le.{0} (0 : Real) Cd →
                ∃ (Cplacement : Real),
                  And (LT.lt.{0} (0 : Real) Cplacement)
                    (∃ (N₀ : Nat),
                      ∀ {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
                        (B : Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag Phead) Band)
                        (R :
                          Erdos390.WholePaper.BankPaperRealization (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                            (Erdos390.WholePaper.upperEndpoint (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                              (Erdos390.WholePaper.upperTailLength c (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))))
                        (certificate :
                          Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                            (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                            (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                        (Tsource : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                        (hlo :
                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) sigma)
                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
                        (hhi :
                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) sigma)
                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
                        {q0 A0 : Real} {d : Int} {exponent : Nat} {activeHeadTarget : ↥Phead → Real}
                        (H : Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.{u_1} B I q0 A0 d exponent activeHeadTarget) (deltaStar betaProt qTilde : Real),
                        LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) →
                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) W →
                            ∀
                              (hsep :
                                LT.lt.{0}
                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
                              (hremaining :
                                ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag Phead)),
                                  Finset.Nonempty.{0}
                                    (SDiff.sdiff.{0}
                                      (Erdos390.Full.PaperGuardCensus.rawCell.{0} Patterns I
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) cell)
                                      (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                        (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))))),
                              Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                                  (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} Patterns I (W :=
                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                    (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))) hsep hremaining) →
                                Eq.{1} qTilde
                                    (Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                      betaAct) →
                                  LE.le.{0} deltaStar (1 : Real) →
                                    (∀ (m : Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)),
                                        Membership.mem.{0, 0} (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat))
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) m)) →
                                      (∀ (m : Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)),
                                          Membership.mem.{0, 0}
                                            (Erdos390.WholePaper.roughBroadLowerBlock
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                              (Erdos390.WholePaper.upperTailLength c
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                              (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) m)) →
                                        Finset.Nonempty.{0}
                                            (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                              (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat)) →
                                          Eq.{1} q0
                                              (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedActiveMass.{u_1} B (K := HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) R certificate
                                                deltaStar betaProt (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, u_1} B c K0 betaProt betaAct) qTilde) →
                                            LE.le.{0} (abs.{0} (↑d : Real))
                                                (HMul.hMul.{0, 0, 0} Cd
                                                  (HDiv.hDiv.{0, 0, 0}
                                                    (Erdos390.WholePaper.secondOrderScale
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} B))) →
                                              ∀
                                                (p :
                                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))),
                                                (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                    LE.le.{0}
                                                      (Erdos390.Full.FiniteProbability.expect.{0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{0, u_1} B (Prod.mk.{0, 0} Option.none.{0} sigma))
                                                        fun
                                                          (m :
                                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                                                              (Prod.mk.{0, 0} Option.none.{0} sigma)) =>
                                                        Erdos390.Full.ArithmeticModel.valuation (↑p : Nat) (↑m : Nat))
                                                      (HDiv.hDiv.{0, 0, 0} Azero (↑(↑p : Nat) : Real))) →
                                                  LE.le.{0}
                                                    (abs.{0}
                                                      (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment.{0, u_1} B (K :=
                                                        HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) R certificate deltaStar betaProt
                                                        (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalTopFrozenRoundedSourceSelector.{u_1} B (K := HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) R
                                                          certificate Tsource deltaStar betaProt
                                                          (Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, u_1} B c K0 betaProt betaAct)
                                                          (HAdd.hAdd.{0, 0, 0} betaProt betaAct) qTilde)
                                                        (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightActiveSeed.{u_1} B I hlo hhi H) (↑p : Nat)))
                                                    (HMul.hMul.{0, 0, 0} Cplacement
                                                      (HDiv.hDiv.{0, 0, 0}
                                                        (Erdos390.WholePaper.secondOrderScale
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                                        (HMul.hMul.{0, 0, 0} (↑(↑p : Nat) : Real) (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} B)))))

noncomputable def Erdos390.RemainingAnalyticGoal007_013 : Prop :=
∀ (Phead : Finset.{0} Nat) (Patterns : Erdos390.Full.PaperHeadSimplex.Tag Phead → Erdos390.Full.HeadPattern.Pattern) (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (G : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (W K0 depth : Nat),
  LT.lt.{0} (1 : Nat) W →
    (∀ (h : Erdos390.Full.PaperHeadSimplex.Tag Phead) (q : Nat), Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Patterns h)) q → LE.le.{0} q W) →
      ∀ {c : Real},
        LT.lt.{0} (0 : Real) c →
          ∀ (betaAct Azero : Real),
            LE.le.{0} (0 : Real) Azero →
              ∃ (Csource : Real),
                And (LT.lt.{0} (0 : Real) Csource)
                  (∃ (N₀ : Nat),
                    ∀ {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
                      (B : Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag Phead) Band)
                      (R :
                        Erdos390.WholePaper.BankPaperRealization (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                          (Erdos390.WholePaper.upperEndpoint (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                            (Erdos390.WholePaper.upperTailLength c (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))))
                      (certificate :
                        Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                          (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                          (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                      (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) (deltaStar betaProt qTilde : Real),
                      LE.le.{0} N₀ (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) →
                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) W →
                          ∀
                            (hsep :
                              LT.lt.{0}
                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))))
                            (hremaining :
                              ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag Phead)),
                                Finset.Nonempty.{0}
                                  (SDiff.sdiff.{0}
                                    (Erdos390.Full.PaperGuardCensus.rawCell.{0} Patterns I
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) cell)
                                    (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                      (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))))),
                            Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                                (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} Patterns I (W :=
                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                  (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))) hsep hremaining) →
                              Eq.{1} qTilde
                                  (Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                    betaAct) →
                                LE.le.{0} deltaStar (1 : Real) →
                                  (∀ (m : Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)),
                                      Membership.mem.{0, 0} (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat))
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B) m)) →
                                    Finset.Nonempty.{0}
                                        (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)) (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat))
                                          (1 : Nat)) →
                                      ∀
                                        (p :
                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B))),
                                        (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                            LE.le.{0}
                                              (Erdos390.Full.FiniteProbability.expect.{0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.guardedCellProbability.{0, u_1} B (Prod.mk.{0, 0} Option.none.{0} sigma))
                                                fun
                                                  (m :
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)
                                                      (Prod.mk.{0, 0} Option.none.{0} sigma)) =>
                                                Erdos390.Full.ArithmeticModel.valuation (↑p : Nat) (↑m : Nat))
                                              (HDiv.hDiv.{0, 0, 0} Azero (↑(↑p : Nat) : Real))) →
                                          Erdos390.WholePaper.BankPaperRealization.RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound.{u_1} B K0 R certificate T deltaStar betaProt
                                            betaAct qTilde (↑p : Nat)
                                            (HMul.hMul.{0, 0, 0} Csource
                                              (HDiv.hDiv.{0, 0, 0}
                                                (Erdos390.WholePaper.secondOrderScale
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1} B)))
                                                (HMul.hMul.{0, 0, 0} (↑(↑p : Nat) : Real) (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1} B)))))


