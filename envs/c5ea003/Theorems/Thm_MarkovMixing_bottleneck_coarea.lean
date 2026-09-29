-- Prove2me | Theorems.Thm_MarkovMixing_bottleneck_coarea
-- name    : MarkovMixing.bottleneck_coarea
-- status  : Proved
-- author  : @chenmin
-- created : 2026-08-22T16:45:44.503387+00:00
-- url     : https://prove2.me/theorems/438e737c-e644-4227-b8dc-602da35fe036
-- title:
--   Lemma 13.17: a discrete co-area inequality for the bottleneck ratio
-- statement:
--   Let $P$ be an irreducible transition matrix on a finite state space $V$, reversible with respect to its stationary distribution $\pi$, and write $Q(x,y) = \pi(x)P(x,y)$ for the edge measure and
--   $$\Phi_\star = \min\Bigl\{\tfrac{Q(S,S^c)}{\pi(S)} : S \ne \emptyset,\ \pi(S) \le \tfrac12\Bigr\}$$
--   for the bottleneck ratio of the chain.
--
--   **Claim.** Let $\psi : V \to \mathbb{R}$ be nonnegative and suppose its support is small, $\pi\{\psi > 0\} \le \tfrac12$. Then
--   $$\Phi_\star \cdot \mathbb E_\pi(\psi) \;\le\; \sum_{x,y \in V} \bigl(\psi(x)-\psi(y)\bigr)^{+} Q(x,y),$$
--   where $a^{+} = \max(a,0)$.
--
--   In words: the total mass of $\psi$ is controlled by how much $\psi$ decreases across the edges of the chain, at the rate set by the worst bottleneck. It is a discrete co-area inequality — the proof applies the definition of $\Phi_\star$ to each super-level set $S_t = \{\psi > t\}$, which is legitimate because $S_t \subseteq \{\psi > 0\}$ has stationary measure at most $\tfrac12$, and then integrates the resulting bound $\Phi_\star\,\pi\{\psi>t\} \le \sum_{x,y} Q(x,y)\mathbb 1\{\psi(x) > t \ge \psi(y)\}$ over $t \in (0,\infty)$, using $\int_0^\infty \mathbb 1\{\psi(x)>t\ge\psi(y)\}\,dt = (\psi(x)-\psi(y))^{+}$.
--
--   This is Lemma 13.17 of Levin--Peres--Wilmer, the engine behind the hard half $\Phi_\star^2/2 \le \gamma$ of the discrete Cheeger inequality: applied to $\psi = f^2$, where $f$ is the positive part of a $\lambda_2$-eigenfunction, together with the Cauchy--Schwarz inequality it converts the bottleneck ratio into a bound on the Dirichlet form.
--
--   **Formalization note.** LPW state the right-hand side as $\sum_{x<y}[\psi(x)-\psi(y)]Q(x,y)$ after choosing a linear order on $V$ that makes $\psi$ non-increasing. For such an order, and using the symmetry of $Q$, that sum equals the order-free expression above: pairs with $\psi(x) \le \psi(y)$ contribute nothing to either side.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.3.3, Lemma 13.17, p. 178 (the sum over x<y for a psi-decreasing order is rewritten order-free with positive parts)

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower

namespace MarkovMixing

/-- **Lemma 13.17** (LPW): for a nonnegative `ψ` supported on a set of
stationary measure at most `1/2`, the mean of `ψ` is controlled by the
`Q`-weighted total decrease of `ψ` across edges, at rate `Φ⋆`:
`Φ⋆ · E_π(ψ) ≤ ∑_{x,y} (ψ(x) − ψ(y))⁺ Q(x,y)`.  LPW order the state space so
that `ψ` is non-increasing and sum over `x < y`; taking positive parts makes
the statement independent of that ordering. -/
theorem bottleneck_coarea {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (ψ : V → ℝ) (hψ : ∀ x : V, 0 ≤ ψ x)
    (hsupp : ∑ x ∈ Finset.univ.filter (fun x : V => 0 < ψ x), π x ≤ 2⁻¹) :
    bottleneckStar P π * distExp π ψ ≤
      ∑ x, ∑ y, max (ψ x - ψ y) 0 * edgeMeasure P π x y := by
  sorry

end MarkovMixing
