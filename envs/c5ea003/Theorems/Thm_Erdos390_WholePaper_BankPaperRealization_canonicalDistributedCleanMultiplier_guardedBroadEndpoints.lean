-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_canonicalDistributedCleanMultiplier_guardedBroadEndpoints
-- name    : Erdos390.WholePaper.BankPaperRealization.canonicalDistributedCleanMultiplier_guardedBroadEndpoints
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:39.174579+00:00
-- url     : https://prove2.me/theorems/99d7fd9b-2916-4711-b461-3a58fd8c3abb
-- title:
--   Clean multiplier endpoints lie in guarded broad pools
-- statement:
--   Fix canonical bank and anchor data $(c,\mathrm{depth},n,W,K,R)$ and a real $\delta$. Take any distributed tangent split request for any flow and real splitting parameters $L,\sigma$. If $m$ belongs to its canonical clean multiplier list formed with tail height $h_n(c)$, exceptional cutoff $X_0(n,\delta)$, dedicated rows and numerical guard set including the fixed exceptional factors, write $u,v$ for its endpoint prime labels and $\ell=\operatorname{rough}_{y(n)}(m)$. Then
--   $$um,vm\in\mathcal P_{\ell}^{\rm guarded,broad},\qquad \ell\ne1\Longrightarrow\ell\text{ is active and nonexceptional}.$$
--   The pool uses the same certificate, $\delta,W,K$.
--
--   This verifies endpoint closure in the guarded candidate geometry before choosing multipliers.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalTangentSlackIntegration.lean#L286-L452

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

theorem Erdos390.WholePaper.BankPaperRealization.canonicalDistributedCleanMultiplier_guardedBroadEndpoints :
∀ {c : Real} {depth n W K : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (deltaStar : Real)
  {flow :
    Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W →
      Erdos390.WholePaper.BankPaperCanonicalTangentPrime n W → Real}
  {L sigma : Real} (request : Erdos390.WholePaper.BankPaperCanonicalDistributedTangentSplitRequest flow L sigma)
  {common : Nat},
  Membership.mem.{0, 0}
      (Erdos390.WholePaper.tangentSplitCleanMultiplierLists.{0} (Erdos390.WholePaper.tangentPositiveFlowEdges.{0} flow)
        (Erdos390.WholePaper.tangentStarEdgeSource.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel)
        (Erdos390.WholePaper.tangentStarEdgeTarget.{0} Erdos390.WholePaper.bankPaperCanonicalTangentPrimeLabel) L sigma
        (fun edge => flow edge.1 edge.2) n K (Erdos390.WholePaper.upperTailLength c n)
        (Erdos390.WholePaper.roughHeadModulus W) (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
        (Erdos390.Full.ArithmeticModel.yNat n) (Erdos390.WholePaper.BankPaperRealization.tangentPaperDedicatedRows R)
        (Erdos390.WholePaper.BankPaperRealization.tangentPaperNumericalGuardSet R certificate
          (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
        request)
      common →
    And
      (And
        (Membership.mem.{0, 0}
          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K
            (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common))
          (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestSource request) common))
        (Membership.mem.{0, 0}
          (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedBroadCorrectionPool R certificate deltaStar W K
            (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common))
          (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalDistributedTangentRequestTarget request) common)))
      (Ne.{1} (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common) (1 : Nat) →
        Erdos390.WholePaper.BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel n deltaStar
          (Erdos390.WholePaper.completeRoughLabel (Erdos390.Full.ArithmeticModel.yNat n) common)) := by sorry
