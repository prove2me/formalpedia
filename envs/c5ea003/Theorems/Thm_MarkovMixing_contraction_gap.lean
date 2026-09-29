-- Prove2me | Theorems.Thm_MarkovMixing_contraction_gap
-- name    : MarkovMixing.contraction_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:46:39.806025+00:00
-- url     : https://prove2.me/theorems/fe30c86c-99b1-45f0-98d6-0c4aa644e324
-- title:
--   Theorem 13.1 -- spectral gap from contracting couplings
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$, and let $\rho$ be a **metric** on $V$: symmetric, vanishing exactly on the diagonal, and satisfying the triangle inequality. A **coupling** of the two one-step distributions $P(x,\cdot)$ and $P(y,\cdot)$ is a probability distribution $q$ on pairs whose marginals are those two rows — the joint law of one step of two copies of the chain, from $x$ and from $y$. Among the eigenvalues of $P$ — the real $\lambda$ admitting a nonzero $f$ with $Pf=\lambda f$ — let $\lambda_\star$ denote the largest absolute value of an eigenvalue different from $1$, so that $\gamma_\star=1-\lambda_\star$ is the absolute spectral gap.
--
--   The theorem (Theorem 13.1 of Levin–Peres–Wilmer) asserts: if for some contraction factor $\theta\ge0$ every pair of states admits a coupling of its one-step distributions that contracts the metric in expectation,
--   $$\mathbb E_q\bigl[\rho(X_1,Y_1)\bigr]\le\theta\,\rho(x,y)\qquad\text{for all }x,y,$$
--   then $\lambda_\star\le\theta$ — equivalently, $\gamma_\star\ge1-\theta$.
--
--   A contracting coupling forces a spectral gap: the geometric decay of distances under the coupling leaves no room for an eigenfunction to decay slower than $\theta^t$. This turns the path-coupling constructions of earlier chapters directly into eigenvalue estimates.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.1, Theorem 13.1, p. 171

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Theorem 13.1** (LPW): if for some metric `ρ` on the state space there
is, for every pair of states, a coupling of the one-step distributions that
contracts `ρ` by a factor `θ`, then every eigenvalue other than `1` has
absolute value at most `θ` — that is, `γ⋆ ≥ 1 − θ`. -/
theorem contraction_gap {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y)
    (hρsymm : ∀ x y : V, ρ x y = ρ y x)
    (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (Q : V → V → (V × V → ℝ))
    (hQ : ∀ x y : V, IsCoupling (rowDist P 1 x) (rowDist P 1 y) (Q x y))
    (hcontract : ∀ x y : V, ∑ p : V × V, Q x y p * ρ p.1 p.2 ≤ θ * ρ x y) :
    lambdaStar P ≤ θ := by
  sorry

end MarkovMixing
