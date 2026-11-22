-- Prove2me | Theorems.Thm_Erdos390_SourceJointConstruction_exists_common_depth
-- name    : Erdos390.SourceJointConstruction.exists_common_depth
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T10:41:26.269183+00:00
-- url     : https://prove2.me/theorems/663da2cf-aff5-43d4-adbc-b5cd417bb682
-- title:
--   A common depth for guarded bank capacity and post-tangent continuation
-- statement:
--   Let
--
--   $$C_0=\frac{4029639598}{25970038185}.$$
--
--   For every real number $c>C_0$, there is a natural number $d\ge201$ such that both the fixed-depth guarded bank capacity assertion and the canonical post-tangent continuation assertion hold at $(c,d)$:
--
--   $$\exists d\ge201,\quad \mathrm{Capacity}(c,d)\ \land\ \mathrm{Continuation}(c,d).$$
--
--   Here capacity asserts that, for all sufficiently large $n$, there are a compatible signed bank and guarded central-anchor certificate with the specified precharge and upper-tail divisibility identities. Continuation asserts that eventual capacity at this depth can be refined to eventual compatible fractional selections with integral complete rough-row sums, exact prime-valuation balance, the prescribed interval support, and all collision exclusions. The predicates retain the literal objects and conditions defined in the accompanying source interface.
--
--   The same depth must serve both assertions. This statement is obtained from the source's distributed Section 9 terminal by retaining its depth and projecting its capacity and continuation fields; its auxiliary width and tangent parameters are discarded.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareDistributedTerminalConnector.lean#L30-L167 ; project the distributed terminal using to_canonicalCapacityAtDepth and to_postTangentContinuationAtDepth.

import Definitions.Def_erdos390_source_bank_interface

theorem Erdos390.SourceJointConstruction.exists_common_depth
    {c : ℝ} (hc : Erdos390.WholePaper.C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      Erdos390.WholePaper.BankPaperCanonicalCapacityAtDepth c depth ∧
      Erdos390.WholePaper.BankPaperCanonicalPostTangentContinuationAtDepth c depth := by sorry
