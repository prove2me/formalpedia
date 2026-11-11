-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_1_2
-- name    : ZeroFreeRRG.Hardcore.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:37:53.203459+00:00
-- url     : https://prove2.me/theorems/bb4f4456-414a-4ef0-ac8d-fd1e02c9101d
-- title:
--   Theorem 1.2 — random d-regular graphs have no hardcore zeros on D([0, α_RSB(d) − δ], η) with high probability
-- statement:
--   Fix an integer $d\ge3$ and $0<\delta<\alpha_{\mathrm{RSB}}(d)$, where $\alpha_{\mathrm{RSB}}(d)=\inf\{\alpha\in(0,1/2):\exists\nu\in\mathcal P_{\pi_\alpha},\ \mathcal B_{d,\alpha}(\nu)>0\}$ (with $\inf\emptyset=1/2$) is the replica symmetry breaking threshold (32). There is $\eta=\eta(d,\delta)>0$ such that, with probability $1-o_n(1)$ over a uniformly random simple $d$-regular graph $G$ on $[n]$, the hardcore partition function
--   $$Z_G(\alpha)=\sum_{I\text{ independent in }G}\lambda(\alpha)^{|I|},\qquad\lambda(\alpha)=\frac{\alpha(1-\alpha)^{d-1}}{(1-2\alpha)^d},$$
--   has no zero $\alpha\in\mathbb C$ with $\operatorname{dist}(\alpha,[0,\alpha_{\mathrm{RSB}}(d)-\delta])<\eta$.
--
--   This is the paper's first main theorem: a zero-free strip around the whole replica-symmetric range of occupation densities, which by Barvinok's interpolation gives deterministic approximate counting there.
--
--   Differences from the source:
--   - encoding: 'with probability 1 − o_n(1) over G ∼ 𝒢_{n,d}' (uniform simple d-regular graph on [n], admissible n) → the published PottsRapidMixing.WithHighProb d: the fraction of simple d-regular graphs on Fin n with the property tends to 1 along n with n·d even; reason: n ≥ d + 1 holds eventually; vertex set Fin n for [n]; constants are quantified outside the predicate, so they are chosen before n and G
--   - encoding: D(S, η) = {z : inf_{w ∈ S} |z − w| < η} → nbhd S η = {z | ∃ w ∈ S, ‖z − w‖ < η} with S = realSegment 0 (α_RSB(d) − δ); reason: for S compact and nonempty the infimum is attained, so the sets coincide
--   - encoding: Z_G(α) = Z_{G,fug}(λ(α)) undefined at α = 1/2 → lam d (1/2) = 0 by Lean's x / 0 = 0, so Z_G(1/2) = 1; reason: affects only α = 1/2, which lies outside D([0, α_RSB(d) − δ], η) for every η ≤ δ (α_RSB(d) ≤ 1/2); cannot make the goal easier
--   - encoding: α_RSB(d) = inf S_d with inf ∅ = 1/2 (32); 𝒫_π all Borel probability measures on Δ_Ω with mean π → alphaRSB d = if S d = ∅ then 1/2 else sInf (S d); cavityLaws: ProbabilityMeasure on ℝ^Ω null off stdSimplex, coordinatewise mean π; reason: Lean's sInf ∅ = 0 is overridden; S_d ⊆ (0, 1/2) is bounded below
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 3, Theorem 1.2 (threshold: p. 33, eq. (32); proof p. 40, §5.4)

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- **Theorem 1.2** (zero-free region for the hardcore model; Chen, Wang, Zhang, arXiv:2610.40510,
p. 3). For every integer `d ≥ 3` and `0 < δ < α_RSB(d)` there is `η = η(d, δ) > 0` such that, with
probability `1 − o_n(1)` over a uniformly random simple `d`-regular graph `G` on `[n]`, the hardcore
partition function `Z_G(α) = Z_{G,fug}(λ(α))` has no zero `α` in the open `η`-neighbourhood of the
real segment `[0, α_RSB(d) − δ]`. -/
theorem theorem_1_2 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) (hδα : δ < alphaRSB d) :
    ∃ η : ℝ, 0 < η ∧
      PottsRapidMixing.WithHighProb d (fun n G =>
        ∀ α ∈ nbhd (realSegment 0 (alphaRSB d - δ)) η, hardcoreZ d G α ≠ 0) := by sorry

end ZeroFreeRRG.Hardcore
