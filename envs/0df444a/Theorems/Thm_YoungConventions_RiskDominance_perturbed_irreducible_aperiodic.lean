-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_perturbed_irreducible_aperiodic
-- name    : YoungConventions.RiskDominance.perturbed_irreducible_aperiodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:27.898262+00:00
-- url     : https://prove2.me/theorems/f9fa1c30-f823-4cfb-a216-15ae50319386
-- title:
--   $P^\varepsilon$ is irreducible and aperiodic and has a unique stationary distribution
-- statement:
--   Let $\Gamma$ be a finite $n$-person game with nonempty strategy sets, let $1\le k\le m$, let $p$ be a best-reply distribution for sample size $k$, and let $(\lambda,q)$ be an admissible experimentation ($\lambda_i>0$, $q_i(\cdot\mid h)$ of full support).
--   Let $\varepsilon>0$ with $\varepsilon\lambda_i\le1$ for all $i$. Then the perturbed process $P^\varepsilon$ of (2) satisfies:
--   1. $P^\varepsilon$ is a stochastic matrix (nonnegative entries, rows summing to $1$);
--   2. $(P^\varepsilon)^m_{hh'}>0$ for all states $h,h'$ (all players may experiment for $m$ periods in succession), so $P^\varepsilon$ is irreducible;
--   3. $(P^\varepsilon)^{m+1}_{hh}>0$ for every state $h$; together with item 2 the process returns to $h$ in exactly $m$ and in exactly $m+1$ periods, so it is aperiodic;
--   4. $P^\varepsilon$ has exactly one stationary distribution $\mu^\varepsilon$, $\mu^\varepsilon P^\varepsilon=\mu^\varepsilon$.
--
--   This makes the stationary distribution $\mu^\varepsilon$ in the definition of stochastic stability well defined.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 67–68

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_perturbed
import Definitions.Def_YoungConventions_RiskDominance_IsStationaryDistribution

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **`P^ε` is a regular (irreducible, aperiodic) chain with a unique stationary distribution.**
Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 67–68 (PDF pp. 12–13): "Let `h` and `h′` be two distinct states. If `P^ε` is in state
`h` at time `t`, there is a positive probability that all players will experiment for `m` periods in
succession. Thus there is a positive probability that the process arrives at state `h′` at time
`t + m`, so `P^ε` is irreducible. It is aperiodic because the process can move from `h` to `h` in
exactly `m` periods, and also in exactly `m + 1` periods. Hence `P^ε` has a unique stationary
distribution `μ^ε` satisfying the equation `μ^εP^ε = μ^ε`."

For every game, `1 ≤ k ≤ m`, best-reply distribution `p`, admissible `(λ, q)` and `ε > 0` with
`ελᵢ ≤ 1`: `P^ε` is row-stochastic, every entry of `(P^ε)^m` is positive, every diagonal entry of
`(P^ε)^{m+1}` is positive, and `P^ε` has exactly one stationary distribution.

**Formalization Note.** "Irreducible" is stated in the form the page proves, `(P^ε)^m_{hh′} > 0` for
all `h, h′` (including `h = h′`), and "aperiodic" as the return to `h` in exactly `m` and `m + 1`
steps; together these say `P^ε` is primitive. The admissible range of `ε` is `0 < ε` with
`ελᵢ ≤ 1` for all `i`, the range on which (2) is a transition matrix. -/
theorem perturbed_irreducible_aperiodic {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q)
    (ε : ℝ) (hε : 0 < ε) (hεlam : ∀ i, ε * lam i ≤ 1) :
    perturbed p q lam ε ∈ Matrix.rowStochastic ℝ (YoungConventions.AdaptivePlay.History S m) ∧
    (∀ h h' : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ m) h h') ∧
    (∀ h : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ (m + 1)) h h) ∧
    ∃! μ : YoungConventions.AdaptivePlay.History S m → ℝ, IsStationaryDistribution μ (perturbed p q lam ε) := by sorry

end YoungConventions.RiskDominance
