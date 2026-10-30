-- Prove2me | Theorems.Thm_XuDRMDP_Finite_theorem_3_1
-- name    : XuDRMDP.Finite.theorem_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:30:42.757992+00:00
-- url     : https://prove2.me/theorems/94718d65-7076-4a1a-a08e-125219a3149e
-- title:
--   Theorem 3.1 — Distributional optimality and an attained saddle
-- statement:
--   Let $S$ be a finite nonempty staged state set with finite nonempty action sets $A_s$, initial stage consisting of $s^{ini}$ alone, finite horizon $T\ge1$, zero terminal rewards and discount $0<\gamma\le1$. Assume the nested local parameter sets $P_s^1\subseteq\cdots\subseteq P_s^n$ ($n\ge1$) are nonempty, convex and compact sets of valid transition/reward vectors. Local sets may couple all actions. Let $0=\lambda_0\le\lambda_1\le\cdots\le\lambda_n=1$. The local class $C_s$ consists of all Borel probability laws supported on $P_s^n$ with $\mu_s(P_s^i)\ge\lambda_i$, and $C_S$ consists of their statewise product laws. Policies are all history-dependent randomized policies on state/action histories, including null histories. Returns are the independent finite trajectory expectations, subsequently integrated against the parameter law.
--
--   Let $\pi^*$ be any S-robust policy: after every admissible nonterminal history its mixed action maximizes the local worst continuation value in Definition 3.2's backward recursion over $\widehat P_s$. Then:
--
--   1. For every policy $\pi$, $\inf_{\mu\in C_S}W(\pi,\mu)\le\inf_{\mu\in C_S}W(\pi^*,\mu)$.
--   2. There exists one $\mu^*\in C_S$ with
--   $$\sup_{\pi\in\Pi^{HR}}W(\pi,\mu^*)=W(\pi^*,\mu^*)=\inf_{\mu\in C_S}W(\pi^*,\mu).$$
--   The Lean saddle predicate gives membership and the equivalent inequalities $W(\pi,\mu^*)\le W(\pi^*,\mu^*)\le W(\pi^*,\mu)$ for every competitor on each side. Since the witness and the chosen policy belong to their domains, these inequalities assert both equalities and their attainment, using the same witness.
--
--   Differences from the source:
--   - encoding: finite states and state-dependent actions, one-based staged histories, and expected discounted trajectory returns → nonempty Fin types, zero-based stages, total policy extensions on unused histories, and explicit finite trajectory sums followed by Bochner integration; reason: finite relabeling and unused extensions preserve all source instances; compact outer support ensures integrability and finite bounded returns
--   - reading: Definition 3.2 displays (r,p) in the weighted sum but (p,r) in its membership condition → consistent (p,r) coordinates in the reduction set; reason: Lemma 3.3 and its proof fix the intended order; see insight I1
--   - encoding: attained minimum and maximum in the S-robust recursion and infima in distributional optimality → real infima and suprema of nonempty bounded images, and the all-competitor local maximizer predicate; reason: compact sets and finite simplices give finite attained extrema; the predicate retains every maximizing action
--   - reading: Theorem 3.1 prose uses the local subscript C_s → the global product-law class C_S in both conclusions; reason: the displayed integral and the product-law construction in the proof require the global class; see insight I2
--   - encoding: two equalities involving policy supremum and distribution infimum → membership and all-competitor saddle inequalities for the same witness; reason: the witness itself attains each extremum, so the encodings are equivalent
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Theorem 3.1, printed p. 291 (PDF p. 4).

import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
open MeasureTheory

namespace XuDRMDP.Finite

theorem theorem_3_1 {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (π : Policy a) (hπ : SRobust U π) :
    DistributionallyRobust U π ∧ ∃ ν : Measure (Parameters n a), Saddle U π ν := by sorry

end XuDRMDP.Finite
