-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_local_stability
-- name    : MarkovEntanglement.rmab_local_stability
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:23:53.854764+00:00
-- url     : https://prove2.me/theorems/fba8eca6-75cf-4ba7-a2ef-7e73d7fc3609
-- title:
--   Local stability at the mean-field fixed point (Lem. 11, Gast et al. 2023)
-- statement:
--   Assume the index policy, through the explicit mean-field map at activation fraction $\alpha$, satisfies the uniform global attractor property with fixed point $m^\ast$, and that it is non-degenerate in the mean-field sense: the budget runs out strictly inside some state $x$, i.e. $0 < \alpha - \sum_{\nu_y > \nu_x} m^\ast_y < m^\ast_x$. Let $K$ be the matrix of the affine piece of the mean-field map on the priority region of $x$ (Lemma 7). Then:
--
--   1. **$K$ is stable on the tangent space of the simplex** — its powers contract zero-sum vectors geometrically: there are $C \ge 0$ and $\rho < 1$ with $\|v K^t\|_\infty \le C \rho^t \|v\|_\infty$ for every $v$ with $\sum_x v_x = 0$. This is the finite-dimensional meaning of "the spectral radius of the linearised dynamics is strictly less than one". The tangent-space formulation is the well-posed one: the hypothesis pins $K$ down only on configurations, which all satisfy $\sum_x m_x = 1$, so $K$ itself is determined only up to the rank-one gauge $K \mapsto K + \mathbf{1}c^{\top}$ (absorbed by the affine offset $b$), and that gauge moves the spectrum arbitrarily — but it acts trivially on zero-sum vectors, which is where the differences $m - m^\ast$ live.
--   2. **The mean-field iterates reach any prescribed neighbourhood of $m^\ast$ in a number of steps that does not depend on the starting configuration**: for every $\varepsilon > 0$ there is a $T$ with $\|\Phi^T(m) - m^\ast\|_\infty < \varepsilon$ for every configuration $m$ in the simplex.
--
--   Non-degeneracy is what makes part (1) meaningful. It says that at $m^\ast$ some state is served only fractionally, so $m^\ast$ sits in the *interior* of its priority region rather than on a boundary between two affine pieces; the map is therefore genuinely affine in a neighbourhood of the fixed point, with linear part acting as $K$ on the differences.
--
--   The two parts play complementary roles in the proof of Theorem 7. Part (2) supplies a uniform horizon $\tilde{T}$ after which every trajectory of the mean-field dynamics has entered a small ball around $m^\ast$; part (1) then guarantees that once inside, the accumulated amplification of the concentration errors of Lemma 10 no longer grows with the horizon. Together they convert a per-step $1/\sqrt{N}$ fluctuation into an $O(1/\sqrt{N})$ bound on the stationary deviation $\mathbb{E}[\|m - m^\ast\|_\infty]$.
-- source:
--   Nicolas Gast, Bruno Gaujal and Chen Yan, 'Exponential asymptotic optimality of Whittle index policy' (2023), Lemma C.5; cited as Lemma 11 in Chen and Peng, arXiv:2506.02385v3, Appendix I, p. 43

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Lemma 11 (Local Stability; Lemma C.5 of Gast, Gaujal and Yan 2023).  Under the uniform
global attractor property and mean-field non-degeneracy:

(i) the affine piece of the mean-field map at the fixed point is stable on the tangent space
of the simplex — its powers contract the differences `m − m✦` geometrically, the
finite-dimensional meaning of "spectral radius `< 1`" for the linearised dynamics (the matrix
itself is determined by the dynamics only up to a rank-one gauge that moves the spectrum, so
the tangent-space formulation is the well-posed one);

(ii) the mean-field iterates reach any prescribed neighbourhood of `m✦` in a number of steps
that does not depend on the starting configuration.

Non-degeneracy places `m✦` in the interior of its priority region, so the map is genuinely
affine near the fixed point and (i) is meaningful.  Part (i) is what turns the per-step
concentration of Lemma 10 into a bound that does not blow up with the horizon; part (ii)
supplies the uniform horizon at which to apply it. -/
theorem rmab_local_stability
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (x : S) (hx : 0 < mstar x ∧ 0 < α - higherPriorityMass ν mstar x ∧
      α - higherPriorityMass ν mstar x < mstar x)
    (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z) :
    IsStableOnTangent K ∧
      ∀ ε > 0, ∃ T : ℕ, ∀ m : S → ℝ, IsConfiguration m →
        supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) T m z - mstar z) < ε := by
  sorry

/-! ### M7 — Theorem 7, index policies are asymptotically separable -/

end MarkovEntanglement
