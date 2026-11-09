-- Prove2me | Theorems.Thm_ZCDPtoGDP_Sharp_theorem_6
-- name    : ZCDPtoGDP.Sharp.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:05.365949+00:00
-- url     : https://prove2.me/theorems/66f07f91-a2c7-40cc-91f9-c5e88df52cbb
-- title:
--   Theorem 6 — sharp zCDP-to-GDP conversion: every $\rho$-zCDP mechanism is $2\Phi^{-1}(\sigma(t_\rho))$-GDP, attained by randomized response
-- statement:
--   Let $\Phi$ be the standard normal CDF and $\sigma(t)=(1+e^{-t})^{-1}$. Fix $\rho\ge0$.
--
--   1. The equation $\rho=t\tanh(t/2)$ has a unique solution $t=t_\rho\ge0$.
--   2. Put
--   $$\mu_{\mathrm{zCDP}}(\rho)=2\Phi^{-1}(\sigma(t_\rho)).$$
--   Every $\rho$-zCDP mechanism is $\mu_{\mathrm{zCDP}}(\rho)$-GDP. Here a mechanism is any Markov kernel $M$ between arbitrary measurable spaces, with any symmetric neighbouring relation on its input space.
--   3. Randomized response $\mathrm{RR}_{t_\rho}$ on $\{0,1\}$, with $0\sim1$, is $\rho$-zCDP and is not $\mu'$-GDP for any $\mu'<\mu_{\mathrm{zCDP}}(\rho)$.
--
--   So $\mu_{\mathrm{zCDP}}(\rho)$ is the smallest GDP parameter that is valid for every $\rho$-zCDP mechanism. The value $\rho=0$ is included: then $t_\rho=0$ and $\mu_{\mathrm{zCDP}}(0)=0$.
--
--   Differences from the source:
--   - encoding: the defined quantities t_ρ and μ_zCDP(ρ) → clause (i) asserts unique existence, and clauses (ii)–(iii) are stated for every t ≥ 0 with t tanh(t/2) = ρ; reason: by clause (i) that t is t_ρ, so this is the same statement without a choice function
--   - reading: randomized response with parameter t_ρ attains the bound → RR_{t_ρ} is ρ-zCDP and not μ′-GDP for any μ′ < μ_zCDP(ρ); reason: the source reads attainment as "no smaller universal parameter is possible" (p. 6, "the smallest universally valid GDP parameter"; p. 22)
--   - reading: RR_{t_ρ} with its (implicit) neighbouring relation → the relation 0 ∼ 1 on Bool; reason: the source leaves it implicit; the usual Hamming-distance-one adjacency from §2 (p. 4) specializes on a single bit to x ≠ x′; diagonal pairs, if included, impose no additional constraint at the nonnegative privacy budgets in scope
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, Theorem 6, eq. (1), p. 6 (restated with proof pp. 21–22; proof App. B pp. 12–22); standing assumptions §2, p. 4

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy
import Definitions.Def_ZCDPtoGDP_Sharp_Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace ZCDPtoGDP.Sharp

/-- Theorem 6 (Sharp zCDP-to-GDP conversion), p. 6 (proof pp. 12–22).  For `ρ ≥ 0` the
equation `ρ = t tanh(t/2)` has a unique solution `t_ρ ≥ 0`; every `ρ`-zCDP mechanism
(Markov kernel, symmetric neighbouring relation) is `μ_zCDP(ρ) = 2Φ⁻¹(σ(t_ρ))`-GDP; and
randomized response `RR_{t_ρ}` is `ρ`-zCDP but not `μ'`-GDP for any `μ' < μ_zCDP(ρ)`. -/
theorem theorem_6 (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∃! t : ℝ, 0 ≤ t ∧ t * Real.tanh (t / 2) = ρ) ∧
    ∀ t : ℝ, 0 ≤ t → t * Real.tanh (t / 2) = ρ →
      (∀ {X : Type u} {Ω : Type v} [MeasurableSpace X] [MeasurableSpace Ω]
          (adj : X → X → Prop), (∀ x x', adj x x' → adj x' x) →
          ∀ (M : Kernel X Ω) [IsMarkovKernel M],
          IsZCDP adj M ρ → IsGDP adj M (2 * stdNormalQuantile (Real.sigmoid t))) ∧
      IsZCDP rrAdj (randResp t) ρ ∧
      ∀ μ' : ℝ, μ' < 2 * stdNormalQuantile (Real.sigmoid t) → ¬ IsGDP rrAdj (randResp t) μ' := by sorry

end ZCDPtoGDP.Sharp
