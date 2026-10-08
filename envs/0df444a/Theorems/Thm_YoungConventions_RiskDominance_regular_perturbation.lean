-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_regular_perturbation
-- name    : YoungConventions.RiskDominance.regular_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:41.542352+00:00
-- url     : https://prove2.me/theorems/1ef2276b-5e55-4fcc-857a-b64e4403520a
-- title:
--   (2) is a regular perturbation of (1), with resistance = number of mistakes
-- statement:
--   Let $\Gamma$ be a finite $n$-person game with nonempty strategy sets, let $1\le k\le m$, let $p$ be a best-reply distribution for sample size $k$, and let $(\lambda,q)$ be an admissible experimentation ($\lambda_i>0$, $q_i(\cdot\mid h)$ of full support).
--   Then for every pair of states $h,h'$:
--   1. $\displaystyle\lim_{\varepsilon\to0^+}P^\varepsilon_{hh'}=P^0_{hh'}$;
--   2. if $h'$ is a successor of $h$ and $r=r(h,h')$ is the number of mistakes in the transition $h\to h'$, then $\varepsilon^{-r}P^\varepsilon_{hh'}$ converges, as $\varepsilon\to0^+$, to a finite limit $c>0$;
--   3. if $h'$ is not a successor of $h$, then $P^\varepsilon_{hh'}=0$ for every $\varepsilon$.
--
--   Together with the irreducibility and aperiodicity of $P^\varepsilon$, this says that $P^\varepsilon$ is a regular perturbation of $P^0$ in the sense of the Appendix (conditions (6)–(8)), and that the resistance of a one-period transition is the minimum number of mistakes required to make it. This is what reduces Theorem 2 to the general theorem on regular perturbations.
--
--   **Formalization Note** The page says "a regular perturbation of the process $P^\varepsilon$ defined in (1)"; display (1) defines $P^0$, and that corrected reading is stated.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 77 (slip 'P^ε defined in (1)' corrected to P⁰); conditions (6)–(8)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_perturbed
import Definitions.Def_YoungConventions_RiskDominance_numMistakes

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **(2) is a regular perturbation of (1); the resistance of a transition is its number of
mistakes.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 77 (PDF p. 22): "The family `P^ε` defined by (2) in the text is a
regular perturbation of the process `P^ε` defined in (1), and the resistance of a one-period
transition is the minimum number of mistakes required to make it." Conditions (7)–(8) of the same
page: `lim_{ε→0} P^ε_{xy} = P⁰_{xy}`, and `P^ε_{xy} > 0` for some `ε` implies there is `r ≥ 0`
with `0 < lim_{ε→0} ε^{−r} P^ε_{xy} < ∞`, `r` being the resistance of `x → y`.

For every game, `1 ≤ k ≤ m`, best-reply distribution `p`, admissible `(λ, q)` and states `h, h′`:
1. `P^ε_{hh′} → P⁰_{hh′}` as `ε → 0⁺` (condition (7));
2. if `h′` is a successor of `h` and `r` is the number of mistakes in `h → h′`, then
   `ε^{−r} P^ε_{hh′}` converges to a positive finite limit as `ε → 0⁺` (condition (8), with
   resistance `r`);
3. if `h′` is not a successor of `h`, then `P^ε_{hh′} = 0` for every `ε` (resistance `∞`).

**Formalization Note.** **Corrected slip:** the page says "regular perturbation of the process `P^ε`
defined in (1)"; display (1) defines `P⁰`, which is what is stated here. Condition (6)
(irreducibility and aperiodicity) is milestone `perturbed_irreducible_aperiodic`. The number of
mistakes is the minimum number of mistakes required to make the transition, since every
non-mistaken component has positive probability without experimentation. -/
theorem regular_perturbation {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q)
    (h h' : YoungConventions.AdaptivePlay.History S m) :
    Tendsto (fun ε => perturbed p q lam ε h h') (𝓝[>] 0) (𝓝 (unperturbed p h h')) ∧
    (YoungConventions.AdaptivePlay.IsSuccessor h h' → ∃ c : ℝ, 0 < c ∧
      Tendsto (fun ε => (ε ^ numMistakes u k h h')⁻¹ * perturbed p q lam ε h h') (𝓝[>] 0) (𝓝 c)) ∧
    (¬ YoungConventions.AdaptivePlay.IsSuccessor h h' → ∀ ε : ℝ, perturbed p q lam ε h h' = 0) := by sorry

end YoungConventions.RiskDominance
