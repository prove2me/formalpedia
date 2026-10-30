-- Prove2me | Theorems.Thm_XuDRMDP_Finite_lemma_3_1
-- name    : XuDRMDP.Finite.lemma_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:30:17.209983+00:00
-- url     : https://prove2.me/theorems/f5f60970-6958-4365-934e-3f8dc716d376
-- title:
--   Lemma 3.1 — Averaged reward-to-go recursion
-- statement:
--   Let $S$ be a finite nonempty staged state set with finite nonempty action sets $A_s$, initial stage consisting of $s^{ini}$ alone, finite horizon $T\ge1$, zero terminal rewards and discount $0<\gamma\le1$. Assume the nested local parameter sets $P_s^1\subseteq\cdots\subseteq P_s^n$ ($n\ge1$) are nonempty, convex and compact sets of valid transition/reward vectors. Local sets may couple all actions. Let $0=\lambda_0\le\lambda_1\le\cdots\le\lambda_n=1$. The local class $C_s$ consists of all Borel probability laws supported on $P_s^n$ with $\mu_s(P_s^i)\ge\lambda_i$, and $C_S$ consists of their statewise product laws. Policies are all history-dependent randomized policies on state/action histories, including null histories. Returns are the independent finite trajectory expectations, subsequently integrated against the parameter law.
--
--   Fix any policy $\pi$, admissible marginal family $(\mu_s)$, its global product law $\mu$, and any admissible history $h_t$ with $t<T$. Write $(\bar p,\bar r)=E_\mu(p,r)$ and
--   $$B_h(x_s)=\sum_{a\in A_s}\pi_h(a)\left[r_{x_s}(a)+\gamma\sum_{j\in S_{t+1}}p_{x_s}(j\mid a)w(\pi,\mu,(h,a,j))\right],\qquad s=s(h).$$
--   Then both equalities hold:
--   $$w(\pi,\mu,h)=\int B_h(x_s)\,d\mu_s(x_s)=B_h(\bar p_s,\bar r_s).$$
--   The history need not have positive probability under the chosen policy or any parameter realization.
--
--   Differences from the source:
--   - encoding: finite states and state-dependent actions, one-based staged histories, and expected discounted trajectory returns → nonempty Fin types, zero-based stages, total policy extensions on unused histories, and explicit finite trajectory sums followed by Bochner integration; reason: finite relabeling and unused extensions preserve all source instances; compact outer support ensures integrability and finite bounded returns
--   - reading: Lemma 3.1 prints “we-” followed by “0 have” → the two displayed equalities with no extra condition; reason: this broken wording is visibly typography, not a mathematical hypothesis
--   - encoding: sum over all next states S in equation (2) → sum restricted by an indicator to the next stage; reason: staged transition probabilities vanish at all other states, including for mean parameters; their impossible continuations contribute zero
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Lemma 3.1, printed p. 291 (PDF p. 4).

import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
open MeasureTheory

namespace XuDRMDP.Finite

theorem lemma_3_1 {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) (U : Uncertainty G) (π : Policy a)
    (μ : Marginals n a) (hμ : admissibleMarginals U μ)
    (h : History a) (hh : Admissible G h) (ht : G.stage h.state + 1 < G.horizon) :
    expectedFrom G π (productLaw μ) h =
      ∫ x, averagedStep G π (productLaw μ) h x ∂(μ h.state) ∧
    (∫ x, averagedStep G π (productLaw μ) h x ∂(μ h.state)) =
      averagedStep G π (productLaw μ) h (globalMean (productLaw μ) h.state) := by sorry

end XuDRMDP.Finite
