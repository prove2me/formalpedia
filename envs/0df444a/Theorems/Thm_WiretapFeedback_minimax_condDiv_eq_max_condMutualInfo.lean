-- Prove2me | Theorems.Thm_WiretapFeedback_minimax_condDiv_eq_max_condMutualInfo
-- name    : WiretapFeedback.minimax_condDiv_eq_max_condMutualInfo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:51.894015+00:00
-- url     : https://prove2.me/theorems/1f9826bc-5130-486a-bc26-678e379c22f8
-- title:
--   Proof of Theorem 1 — the minimax chain $\min_V\max_{P_X}D(W\|V|P_X)=\max_{P_X}I(X\wedge Y|Z)$
-- statement:
--   Let $W:\mathcal X\to\mathcal Y\times\mathcal Z$ be a wiretap channel on finite alphabets with $\mathcal X$ nonempty, written $W(y,z|x)=W_2(z|x)W_1(y|z,x)$. Then
--   $$
--   \begin{aligned}
--   \min_V\max_{P_X}D(W\|V|P_X)&=\min_{V_1}\max_{P_X}D(W_1\|V_1|P_XW_2)=\max_{P_X}\min_{V_1}D(W_1\|V_1|P_XW_2)\\
--   &=\max_{P_X}D(P_{Y|ZX}\|P_{Y|Z}|P_{ZX})=\max_{P_X}I(X\wedge Y|Z),
--   \end{aligned}
--   $$
--   where $P_{XYZ}$ is given by $P_XW$ and $V$ ranges over the channels $V(y,z|x)=V_2(z|x)V_1(y|z)$ of Theorem 6.
--
--   Together with Theorems 4 and 6 this identity yields Theorem 1: the best exponent of the active test against a degraded-form alternative is exactly $\max_{P_X}I(X\wedge Y|Z)$.
--
--   **Formalization Note** Minima and maxima are infima and suprema in the extended reals (all are attained); the minimum over $V$ is over all pairs $(V_2,V_1)$. Conditional divergences are in joint form, as in the per-$P_X$ step. All four equalities are stated.
--
--   Differences from the source:
--   - encoding: max over P_X (presupposes an input distribution) → [Nonempty X]; reason: excludes only the empty input alphabet, where max_{P_X} is undefined; there the first expression would be +∞ when Y is empty
--   - encoding: min/max → ⨅/⨆ in EReal; reason: Lean convention; all are attained
--   - encoding: D(W‖V|P_X), D(W₁‖V₁|P_X W₂), D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX}) → joint forms D(P_X W‖P_X V), D(P_X W‖P_X W₂ V₁), D(P_{XYZ}‖P_{XZ}P_{YZ}/P_Z); reason: chain-rule identities; same values
--   - encoding: min over V with V(y,z|x) = V₂(z|x)V₁(y|z) → ⨅ over channels V₂ : X → Z and V₁ : Z → Y of degradedChannel V₂ V₁; reason: the same set of channels V
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §V, p.3, proof of Theorem 1 (the displayed chain)

import Mathlib
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WiretapFeedback_condDiv
import Definitions.Def_WiretapFeedback_degradedChannel
import Definitions.Def_WiretapFeedback_eveMarginal

namespace WiretapFeedback

/-- **Proof of Theorem 1, the minimax chain** (Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, p. 3):
for `W(y, z|x) = W₂(z|x) W₁(y|z, x)`,
`min_V max_{P_X} D(W‖V|P_X) = min_{V₁} max_{P_X} D(W₁‖V₁|P_X W₂) = max_{P_X} min_{V₁} D(W₁‖V₁|P_X W₂)
= max_{P_X} D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX}) = max_{P_X} I(X ∧ Y | Z)`, where `P_{XYZ}` is given by
`P_X W`, and `V` ranges over the channels `V(y, z|x) = V₂(z|x) V₁(y|z)` of Theorem 6.

**Formalization Note** `min`/`max` are `⨅`/`⨆` in `EReal` (all are attained). The minimization
over `V` is over all pairs of channels `V₂ : X → Z`, `V₁ : Z → Y`; `W₂` is `eveMarginal W`.
`D(W₁‖V₁|P_X W₂)` is the joint form `condDiv W (degradedChannel W₂ V₁) P_X = D(P_X W‖P_X W₂ V₁)`
and `D(P_{Y|ZX}‖P_{Y|Z}|P_{ZX})` the joint form `D(P_{XYZ}‖P_{XZ} P_{YZ}/P_Z)` (chain rule). All
four equalities are stated. The input alphabet is nonempty (`[Nonempty X]`), as `max_{P_X}`
presupposes; with `X` and `Y` empty and `Z` nonempty the first expression would be an infimum
over no `V₁` (`+∞`) and the last a supremum over no `P_X` (`−∞`). -/
theorem minimax_condDiv_eq_max_condMutualInfo {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y]
    [Fintype Z] (W : WildeQIT.Channel X (Y × Z)) :
    ((⨅ (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y),
        ⨆ p : WildeQIT.FinDist X, condDiv W (degradedChannel V₂ V₁) p) =
      ⨅ V₁ : WildeQIT.Channel Z Y,
        ⨆ p : WildeQIT.FinDist X, condDiv W (degradedChannel (eveMarginal W) V₁) p) ∧
    ((⨅ V₁ : WildeQIT.Channel Z Y,
        ⨆ p : WildeQIT.FinDist X, condDiv W (degradedChannel (eveMarginal W) V₁) p) =
      ⨆ p : WildeQIT.FinDist X,
        ⨅ V₁ : WildeQIT.Channel Z Y, condDiv W (degradedChannel (eveMarginal W) V₁) p) ∧
    ((⨆ p : WildeQIT.FinDist X,
        ⨅ V₁ : WildeQIT.Channel Z Y, condDiv W (degradedChannel (eveMarginal W) V₁) p) =
      ⨆ p : WildeQIT.FinDist X, WildeQIT.relEntropy (jointLaw p W)
        (fun t => (jointLaw p W).margXZ.prob (t.1, t.2.2) * (jointLaw p W).margYZ.prob t.2 /
          (jointLaw p W).margYZ.snd.prob t.2.2)) ∧
    ((⨆ p : WildeQIT.FinDist X, WildeQIT.relEntropy (jointLaw p W)
        (fun t => (jointLaw p W).margXZ.prob (t.1, t.2.2) * (jointLaw p W).margYZ.prob t.2 /
          (jointLaw p W).margYZ.snd.prob t.2.2)) =
      ⨆ p : WildeQIT.FinDist X, ((WildeQIT.condMutualInfo (jointLaw p W) : ℝ) : EReal)) := by sorry

end WiretapFeedback
