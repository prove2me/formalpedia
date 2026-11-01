-- Prove2me | Theorems.Thm_WiretapFeedback_iInf_condDiv_eq_condMutualInfo
-- name    : WiretapFeedback.iInf_condDiv_eq_condMutualInfo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:49.166302+00:00
-- url     : https://prove2.me/theorems/1094734c-5aa0-43b9-9fa7-3167c8959456
-- title:
--   Proof of Theorem 1, per-$P_X$ step — $\min_{V_1}D(W_1\|V_1|P_XW_2)=I(X\wedge Y|Z)$
-- statement:
--   Let $W:\mathcal X\to\mathcal Y\times\mathcal Z$ be a wiretap channel on finite alphabets, written $W(y,z|x)=W_2(z|x)W_1(y|z,x)$ with $W_2$ the eavesdropper's marginal, and let $P_X$ be an input distribution; let $P_{XYZ}=P_XW$. Then
--   $$
--   \min_{V_1}D\bigl(W_1\|V_1\big|P_XW_2\bigr)=D\bigl(P_{Y|ZX}\|P_{Y|Z}\big|P_{ZX}\bigr)=I(X\wedge Y|Z),
--   $$
--   the minimum running over all channels $V_1:\mathcal Z\to\mathcal Y$, and $I(X\wedge Y|Z)$ being the conditional mutual information in bits.
--
--   These are the third-to-fifth expressions of the chain in the proof of Theorem 1, for a fixed $P_X$.
--
--   **Formalization Note** Conditional divergences are in joint form: $D(W_1\|V_1|P_XW_2)=D(P_XW\,\|\,P_XW_2V_1)$, and $D(P_{Y|ZX}\|P_{Y|Z}|P_{ZX})=D(P_{XYZ}\|P_{XZ}P_{YZ}/P_Z)$; the minimum is an infimum in the extended reals.
--
--   Differences from the source:
--   - encoding: D(W₁‖V₁|P_X W₂) with W₁(y|z,x) = W(y,z|x)/W₂(z|x) → condDiv W (degradedChannel W₂ V₁) P_X = D(P_X W ‖ P_X W₂ V₁); reason: chain rule: the W₂ factors cancel; same value, and W₁ is never formed
--   - encoding: D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX}) → relEntropy P_{XYZ} (P_{XZ}·P_{YZ}/P_Z); reason: joint form of the conditional divergence; where P_Z(z) = 0 the junk quotient 0 meets P_{XYZ} = 0
--   - encoding: min over V₁ → ⨅ over all channels V₁ : Z → Y in EReal; reason: the minimum is attained at V₁ = P_{Y|Z}
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, p.3, proof of Theorem 1 (third to fifth expressions of the chain)

import Mathlib
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WiretapFeedback_condDiv
import Definitions.Def_WiretapFeedback_degradedChannel
import Definitions.Def_WiretapFeedback_eveMarginal

namespace WiretapFeedback

/-- **Proof of Theorem 1, the per-`P_X` step** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3,
third to fifth expressions of the chain): writing `W(y, z|x) = W₂(z|x) W₁(y|z, x)`, for every input
distribution `P_X`,
`min_{V₁} D(W₁‖V₁|P_X W₂) = D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX}) = I(X ∧ Y | Z)`, where `P_{XYZ}` is given by
`P_X W`.

**Formalization Note** `W₂` is `eveMarginal W`. With the joint form of the conditional
divergence, `D(W₁‖V₁|P_X W₂) = D(P_X W ‖ P_X W₂ V₁) = condDiv W (degradedChannel W₂ V₁) P_X` by the
chain rule (the `W₂` factors cancel), so the quotient `W₁` is never formed. Likewise
`D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX})` is the joint form `D(P_{XYZ} ‖ P_{XZ} P_{YZ} / P_Z)`; where
`P_Z(z) = 0` the (junk) quotient is `0`, and there `P_{XYZ}` vanishes too. `min` is `⨅` in `EReal`
over all channels `V₁ : Z → Y`; `I(X ∧ Y | Z)` is `WildeQIT.condMutualInfo` (bits) of `P_X W` on
`X × Y × Z`. Both equalities are stated. -/
theorem iInf_condDiv_eq_condMutualInfo {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) (p : WildeQIT.FinDist X) :
    let P := jointLaw p W
    (⨅ V₁ : WildeQIT.Channel Z Y, condDiv W (degradedChannel (eveMarginal W) V₁) p) =
        WildeQIT.relEntropy P
          (fun t => P.margXZ.prob (t.1, t.2.2) * P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) ∧
      WildeQIT.relEntropy P
          (fun t => P.margXZ.prob (t.1, t.2.2) * P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) =
        ((WildeQIT.condMutualInfo P : ℝ) : EReal) := by sorry

end WiretapFeedback
