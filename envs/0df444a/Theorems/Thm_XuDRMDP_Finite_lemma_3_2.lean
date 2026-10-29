-- Prove2me | Theorems.Thm_XuDRMDP_Finite_lemma_3_2
-- name    : XuDRMDP.Finite.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:30:37.731016+00:00
-- url     : https://prove2.me/theorems/1b32351b-a664-4338-9cdd-4ccdcfe32e4c
-- title:
--   Lemma 3.2 — Evaluation at mean parameters
-- statement:
--   Let $S$ be a finite nonempty staged state set with finite nonempty action sets $A_s$, initial stage consisting of $s^{ini}$ alone, finite horizon $T\ge1$, zero terminal rewards and discount $0<\gamma\le1$. Assume the nested local parameter sets $P_s^1\subseteq\cdots\subseteq P_s^n$ ($n\ge1$) are nonempty, convex and compact sets of valid transition/reward vectors. Local sets may couple all actions. Let $0=\lambda_0\le\lambda_1\le\cdots\le\lambda_n=1$. The local class $C_s$ consists of all Borel probability laws supported on $P_s^n$ with $\mu_s(P_s^i)\ge\lambda_i$, and $C_S$ consists of their statewise product laws. Policies are all history-dependent randomized policies on state/action histories, including null histories. Returns are the independent finite trajectory expectations, subsequently integrated against the parameter law.
--
--   For every policy $\pi$ and every $\mu\in C_S$, let $(\bar p,\bar r)=E_\mu(p,r)$. Then
--   $$W(\pi,\mu)=u(\pi,\bar p,\bar r).$$
--   The left side integrates the independently defined trajectory return. The right side evaluates that same path sum at the mean parameter vector. No optimality, Markov property, or deterministic-action restriction is imposed on $\pi$.
--
--   Differences from the source:
--   - encoding: finite states and state-dependent actions, one-based staged histories, and expected discounted trajectory returns → nonempty Fin types, zero-based stages, total policy extensions on unused histories, and explicit finite trajectory sums followed by Bochner integration; reason: finite relabeling and unused extensions preserve all source instances; compact outer support ensures integrability and finite bounded returns
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Lemma 3.2, printed p. 292 (PDF p. 5).

import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
open MeasureTheory

namespace XuDRMDP.Finite

theorem lemma_3_2 {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (π : Policy a)
    (ν : Measure (Parameters n a)) (hν : ν ∈ globalClass U) :
    performance G π ν = totalReturn G π (globalMean ν) := by sorry

end XuDRMDP.Finite
