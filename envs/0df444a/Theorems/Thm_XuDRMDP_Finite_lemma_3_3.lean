-- Prove2me | Theorems.Thm_XuDRMDP_Finite_lemma_3_3
-- name    : XuDRMDP.Finite.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:30:40.710986+00:00
-- url     : https://prove2.me/theorems/899aee1f-5ad4-4be2-9951-0ff76f338478
-- title:
--   Lemma 3.3 — Exact attainable mean set
-- statement:
--   Let $S$ be a finite nonempty staged state set with finite nonempty action sets $A_s$, initial stage consisting of $s^{ini}$ alone, finite horizon $T\ge1$, zero terminal rewards and discount $0<\gamma\le1$. Assume the nested local parameter sets $P_s^1\subseteq\cdots\subseteq P_s^n$ ($n\ge1$) are nonempty, convex and compact sets of valid transition/reward vectors. Local sets may couple all actions. Let $0=\lambda_0\le\lambda_1\le\cdots\le\lambda_n=1$. The local class $C_s$ consists of all Borel probability laws supported on $P_s^n$ with $\mu_s(P_s^i)\ge\lambda_i$, and $C_S$ consists of their statewise product laws. Policies are all history-dependent randomized policies on state/action histories, including null histories. Returns are the independent finite trajectory expectations, subsequently integrated against the parameter law.
--
--   For every state $s$, the set of attainable local means is exactly
--   $$\left\{\int x\,d\mu_s(x):\mu_s\in C_s\right\}=\widehat P_s
--   =\left\{\sum_{i=1}^n(\lambda_i-\lambda_{i-1})x_i:x_i\in P_s^i\right\}.$$
--   This is set equality in both directions for the full Borel-law class. Repeated confidence levels, zero increments, identical nested sets and singleton sets are included.
--
--   Differences from the source:
--   - encoding: finite states and state-dependent actions, one-based staged histories, and expected discounted trajectory returns → nonempty Fin types, zero-based stages, total policy extensions on unused histories, and explicit finite trajectory sums followed by Bochner integration; reason: finite relabeling and unused extensions preserve all source instances; compact outer support ensures integrability and finite bounded returns
--   - reading: Definition 3.2 displays (r,p) in the weighted sum but (p,r) in its membership condition → consistent (p,r) coordinates in the reduction set; reason: Lemma 3.3 and its proof fix the intended order; see insight I1
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Lemma 3.3, printed p. 292 (PDF p. 5).

import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
open MeasureTheory

namespace XuDRMDP.Finite

theorem lemma_3_3 {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (s : Fin n) :
    {x | ∃ μ ∈ localClass U s, localMean μ = x} = reducedSet U s := by sorry

end XuDRMDP.Finite
