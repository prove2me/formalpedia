-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_eq6_weighted_average
-- name    : ZhengFedergruenSS.Algorithm.eq6_weighted_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:30.950534+00:00
-- url     : https://prove2.me/theorems/c39e51e1-d11d-4874-a2b0-43e5cdda3864
-- title:
--   §2, (6), p. 656 — c(s − 1, S) is a weighted average of c(s, S) and G(s)
-- statement:
--   In the model of Zheng and Federgruen (demand law with $p_0<1$, fixed cost $K>0$, $-G$ unimodal, the growth condition), let $\alpha_n=M(n)/M(n+1)$. For integers $s<S$ and $n=S-s$,
--   $$0<\alpha_n\le 1,\qquad c(s-1,S)=\alpha_n\,c(s,S)+(1-\alpha_n)\,G(s).$$
--
--   So lowering the reorder level by one moves the cost toward $G(s)$. This identity underlies Lemma 0 and through it every comparison the algorithm makes.
--
--   **Formalization Note.** $\alpha_n=1$ is possible: it happens when $m(n)=0$, e.g. for demand concentrated on $\{0,2\}$. The upper bound is therefore weak, as printed.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 656, §2, (6)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Display (6), §2, p. 656 (Zheng and Federgruen 1991): with `α_n = M(n)/M(n + 1)`,
`0 < α_n ≤ 1` and, for `s < S` and `n = S − s`,
`c(s − 1, S) = α_n c(s, S) + (1 − α_n) G(s)`.

Formalization Note: `α_n` may equal `1` (when `m(n) = 0`, e.g. for demand concentrated on
`{0, 2}`), so the upper bound is weak, as printed. -/
theorem eq6_weighted_average (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (s S : ℤ) (hsS : s < S) :
    0 < alpha D.φ (S - s).toNat ∧ alpha D.φ (S - s).toNat ≤ 1 ∧
      c D.φ K G (s - 1) S =
        alpha D.φ (S - s).toNat * c D.φ K G s S + (1 - alpha D.φ (S - s).toNat) * G s := by sorry

end ZhengFedergruenSS.Algorithm
