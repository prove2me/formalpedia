-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:48.791131+00:00
-- url     : https://prove2.me/theorems/4c644681-72f4-43ef-96d2-6b0e32cd0e97
-- title:
--   Post-tangent output from a collision-free multiplier family
-- statement:
--   Fix a paper bank $R$ and its compatible guarded central-anchor certificate, finite exceptional, fixed and candidate sets, and a real selector $u$. Let a rounded-selector tangent-input certificate be given, including its band map, cell indices and pointwise and prefix residual bounds. Suppose a nonnegative flow on the canonical tangent primes has divergence equal to the selector's canonical tangent residual. Fix $L,\sigma>0$, natural clean-list parameters, and a multiplier $z_q$ in the corresponding clean list for every split positive-flow request $q$.
--
--   Assume both selected endpoint products lie in the candidate set, all these endpoints are distinct, every fixed factor is positive, and the selector tail charge divides the precharged tail target. At both endpoints of every request require $\sigma/L\le u\le1-\sigma/L$. Then there exists a canonical post-tangent output with
--   $$u_{\rm out}=\operatorname{Update}(F,L,\sigma,(z_q),u).$$
--   The output certifies feasibility on the supplied candidate set, integral rough-row sums and the charged valuation identity. The candidate set itself is arbitrary; only the explicit endpoint-membership condition is needed.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalDistributedCandidateSet.lean#L141-L418

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

universe u_1

theorem Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates :
∀ {c : Real} {depth n W K h Phead X0 : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (fixedExceptional fixed candidates : Finset.{0} Nat) (selector : Nat → Real) {Band : Type u_1}
  [inst : DecidableEq.{u_1 + 1} Band] (bandOf : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Band)
  (cellIndex : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Nat)
  (pointwiseUpper : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real) (prefixUpper : Band → Nat → Real),
  Erdos390.WholePaper.BankPaperCanonicalRoundedSelectorTangentInput.{u_1} R certificate fixed candidates bandOf
      cellIndex pointwiseUpper prefixUpper selector →
    ∀
      (flow :
        Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W →
          Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real),
      (∀ (source target : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
          LE.le.{0} (0 : Real) (flow source target)) →
        (∀ (p : Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W),
            Eq.{1} (Erdos390.WholePaper.tangentFlowDivergence.{0} flow p)
              (Erdos390.WholePaper.bankPaperCanonicalTangentResidual R certificate fixed candidates selector p)) →
          ∀ (L sigma : Real),
            LT.lt.{0} (0 : Real) L →
              LT.lt.{0} (0 : Real) sigma →
                (∀ (a : Nat), Membership.mem.{0, 0} fixed a → LT.lt.{0} (0 : Nat) a) →
                  Dvd.dvd.{0} (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R fixed)
                      (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) →
                    ∀
                      (multiplier :
                        Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma → Nat),
                      (∀
                          (request :
                            Erdos390.WholePaper.TangentSplitRequest.{0}
                              (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow) L sigma
                              fun
                                (edge :
                                  Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                    (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                              flow edge.1 edge.2),
                          Membership.mem.{0, 0}
                            (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0}
                              (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow)
                              (Erdos390.WholePaper.tangentStarEdgeSource.{0}
                                Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                              (Erdos390.WholePaper.tangentStarEdgeTarget.{0}
                                Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
                              L sigma
                              (fun
                                  (edge :
                                    Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                      (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                flow edge.1 edge.2)
                              n K h Phead X0 (Erdos390.Full.ArithmeticModel.yNat n)
                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
                              (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate
                                fixedExceptional)
                              request)
                            (multiplier request)) →
                        (∀
                            (request :
                              Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                            And
                              (Membership.mem.{0, 0} candidates
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                  (multiplier request)))
                              (Membership.mem.{0, 0} candidates
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request)
                                  (multiplier request)))) →
                          Erdos390.WholePaper.TangentEndpointsDistinct.{0}
                              (Erdos390.WholePaper.tangentSplitRequests.{0}
                                (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow) L sigma
                                fun
                                  (edge :
                                    Prod.{0, 0} (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)
                                      (Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W)) =>
                                flow edge.1 edge.2)
                              Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource
                              Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget multiplier →
                            (∀
                                (request :
                                  Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                                And
                                  (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                    (selector
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                        (multiplier request))))
                                  (LE.le.{0}
                                    (selector
                                      (HMul.hMul.{0, 0, 0}
                                        (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request)
                                        (multiplier request)))
                                    (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L)))) →
                              (∀
                                  (request :
                                    Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma),
                                  And
                                    (LE.le.{0} (HDiv.hDiv.{0, 0, 0} sigma L)
                                      (selector
                                        (HMul.hMul.{0, 0, 0}
                                          (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget
                                            request)
                                          (multiplier request))))
                                    (LE.le.{0}
                                      (selector
                                        (HMul.hMul.{0, 0, 0}
                                          (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget
                                            request)
                                          (multiplier request)))
                                      (HSub.hSub.{0, 0, 0} (1 : Real) (HDiv.hDiv.{0, 0, 0} sigma L)))) →
                                ∃ (output :
                                  Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput R certificate candidates
                                    fixed),
                                  Eq.{1} (Erdos390.WholePaper.BankPaperCanonicalPostTangentOutput.selector output)
                                    (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentUpdatedSelector flow L
                                      sigma multiplier selector) := by sorry
