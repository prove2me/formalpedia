-- Prove2me | Theorems.Thm_KServer_workFnU_antipodal_extension_restrict
-- name    : KServer.workFnU_antipodal_extension_restrict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:34:36.00243+00:00
-- url     : https://prove2.me/theorems/1439b41a-08b6-4e1a-bce4-e6635224a93d
-- title:
--   The work function of the antipodal extension restricts to the original work function
-- statement:
--   Let $M$ be a metric space with all distances bounded by $\Delta > 0$, and let $M \cup \bar M$ be its antipodal extension --- the space obtained by adjoining a reflected copy of $M$, with $d(\bar p, \bar q) = d(p,q)$ and $d(p, \bar q) = 2\Delta - d(p,q)$. A $k$-server instance on $M$ (initial configuration $C_0$, request sequence $\sigma$) is also an instance on the extension. The theorem says that the extension changes nothing about it:
--
--   $$w^{M \cup \bar M}_{C_0, \sigma}(X) \;=\; w^{M}_{C_0, \sigma}(X) \qquad \text{for every configuration } X \text{ of points of } M,$$
--
--   where $w$ denotes the (unlabelled) work function. Offline solutions gain nothing by parking servers at antipodes.
--
--   ## Why
--
--   One inequality is trivial: an offline schedule in $M$ is a schedule in the extension of the same cost, because $M$ embeds isometrically. For the other, there is a $1$-Lipschitz retraction of the extension onto $M$ --- collapse the reflected copy onto the original, $\bar x \mapsto x$. Between two original points the retraction changes nothing; between $\bar x$ and $\bar y$ it preserves the distance by construction; and between $x$ and $\bar y$ it contracts, since $d(x,y) \le 2\Delta - d(x,y)$ exactly because $\Delta$ bounds the diameter. Applying the retraction to every configuration of an extension schedule yields an $M$-schedule of no greater cost that serves the same requests (which lie in $M$ and are fixed by the retraction) and ends at the same configuration (which lies in $M$). Hence the two infima coincide.
--
--   ## Role
--
--   The Coester--Koutsoupias potential for $k$ servers is a minimum of sums of work-function values at configurations mixing original points with antipodes, so it is a functional of the work function **on the extension**; but the algorithm being analysed, and the competitiveness statement being proved, live on $M$. This identity is the bridge: it lets the offset and update properties, proved for the extension work function, be read as statements about the original work function at every configuration the analysis actually charges --- and it is why adjoining antipodes is a legitimate proof device rather than a change of problem.
--
--   ## Formalization note
--
--   The extension is `antipodalExtension M Δ hΔ0 hΔ`, a `MetricSpace` structure on the sum type $M \oplus M$; the embedding is `Sum.inl`, applied pointwise to the initial configuration, the requests, and the target configuration. The retraction is `Sum.elim id id`. The statement is for `workFnU`, the work function whose final move is a minimum-cost matching; the labelled version of the identity holds as well and is what the proof establishes first, the unlabelled case following by taking the infimum over relabellings, which commutes with the embedding.
-- source:
--   Implicit in the use of the antipodal extension in E. Koutsoupias, 'Weak adversaries for the k-server problem', FOCS 1999, and C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential': the potential is evaluated on the extension while the algorithm and its competitiveness live on the original space.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem workFnU_antipodal_extension_restrict (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun i => Sum.inl (X i))
      = workFnU C₀ σ X := by sorry

end KServer
