-- Prove2me | Definitions.Def_markov_entanglement_meanfield
-- name    : markov_entanglement_meanfield
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-08-28T02:21:59.479447+00:00
-- url     : https://prove2.me/theorems/ffb37f78-0a08-4c96-ae01-5874fe846133
-- title:
--   The mean-field limit of a restless bandit
-- statement:
--   `markov_entanglement_rmab` characterises the mean-field map $\varphi$ only through the configurations that an actual $N$-agent system can occupy — the points of the simplex whose coordinates are multiples of $1/N$. That is enough to *state* the asymptotic theorems, but not to reason about $\varphi$ as a map on the simplex: the stability analysis of Gast, Gaujal and Yan differentiates $\varphi$, iterates it and takes its spectral radius, all of which need $\varphi$ defined everywhere.
--
--   This layer supplies the missing continuum objects.
--
--   **The mean-field map on the whole simplex.** Under an index policy with priority $\nu$ and activation fraction $\alpha$, the mass sitting in a local state $x$ splits into an activated part and an idle part. The activated part is whatever is left of the budget after every strictly higher-priority state has been served, capped by the mass actually in $x$ and floored at zero:
--
--   $$z_x(m) \;=\; \min\Big(m_x,\ \max\big(0,\ \alpha - \textstyle\sum_{\nu_y > \nu_x} m_y\big)\Big),$$
--
--   and each part then moves by its own kernel:
--
--   $$\varphi(m)_y \;=\; \sum_x \big[(m_x - z_x(m))\,P_0(x,y) + z_x(m)\,P_1(x,y)\big].$$
--
--   No $N$ appears, which is exactly the point: it is the fixed activation *fraction* that makes the map independent of the system size. The companion theorem `meanFieldMap_isMeanFieldMap` checks that this formula agrees with the $N$-agent characterisation whenever $\alpha = M/N$, so the two descriptions are the same map.
--
--   **The priority regions.** The configuration $m$ lies in the priority region of the state $x$ when $x$ is the state the budget runs out in, $\sum_{\nu_y > \nu_x} m_y \le \alpha < \sum_{\nu_y > \nu_x} m_y + m_x$. These $|S|$ regions cover the simplex, and $\varphi$ is affine on each of them — the content of Lemma 7.
--
--   **The limiting local policy.** The activated mass in $x$ as a fraction of the mass in $x$ is the probability with which the mean-field limiting policy activates an agent in state $x$. This is the local policy that the index policy converges to, and the one the local chains in the value decomposition are built from.
--
--   **The finite-horizon law of the process.** One step of the $N$-agent joint state chain draws the joint action from the policy and then moves the agents independently through their own kernels; iterating gives the law after $t$ steps. The concentration lemmas are statements about this law, expressed as finite sums rather than measure-theoretically.
--
--   **Distributions, norms, non-degeneracy and stability.** A plain distribution predicate (nonnegative, summing to one): the stationary occupancy of an index policy vanishes on every non-budgeted action profile, so the strictly positive predicate of the two-agent development is unsatisfiable here — every $\mu$-weighted quantity downstream is stated with products rather than divisions, so nothing needs positivity. The $\ell^1$ norm on configurations, in which the one-step concentration bound is stated (the $\ell^\infty$ bounds reuse `supNorm` from the previous layer). The continuum form of non-degeneracy: the budget runs out strictly inside some state at $m^\ast$, placing the fixed point in the interior of its priority region — the per-$N$ form cannot hold at every $N$ simultaneously (at $N=1$ the budget floors to zero). And stability on the tangent space: the affine piece $K$ at the fixed point is determined by the dynamics only up to the rank-one gauge $K \mapsto K + \mathbf{1}c^{\top}$, which moves the spectrum but acts trivially on zero-sum vectors, so the well-posed notion is geometric contraction of $K$'s powers on the differences $m - m^\ast$.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Appendix I, pp. 41-43

import Definitions.Def_markov_entanglement_rmab

open scoped BigOperators

namespace MarkovEntanglement

/-! ## The mean-field limit of a restless bandit

`Def_markov_entanglement_rmab` characterises the mean-field map `φ` only through the
configurations that an actual `N`-agent system can occupy — the points of the simplex whose
coordinates are multiples of `1/N`.  That is enough to *state* the asymptotic theorems, but
not to reason about `φ` as a map on the simplex: the stability analysis of Gast et al.
differentiates `φ`, iterates it and takes its spectral radius, all of which need `φ` defined
everywhere.

This layer supplies the missing continuum objects.  It gives an explicit formula for the
mean-field map on the whole simplex, and `meanFieldMap_isMeanFieldMap` checks that the
formula agrees with the characterisation of the previous layer on every configuration a real
system can occupy — so the two descriptions are the same map, and the asymptotic theorems may
be proved about the explicit one.

It also supplies the finite-horizon law of the configuration process, which the concentration
lemmas are statements about, and the two norms those lemmas use. -/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The fraction of agents sitting in states of strictly higher priority than `x`.  This is
the continuum counterpart of `higherPriorityCount`. -/
noncomputable def higherPriorityMass (ν : S → ℝ) (m : S → ℝ) (x : S) : ℝ :=
  ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, m y

/-- The fraction of the whole population that an index policy activates out of state `x`:
whatever is left of the budget `α` after every strictly higher-priority state has been served,
capped by the mass actually sitting in `x` and floored at zero.  This is the continuum
counterpart of `activateCount / N`. -/
noncomputable def activateFraction (ν : S → ℝ) (α : ℝ) (m : S → ℝ) (x : S) : ℝ :=
  min (m x) (max 0 (α - higherPriorityMass ν m x))

/-- The **mean-field transition map** on the whole simplex: the mass in each state splits into
the part that is activated and the part that is not, each moving by its own kernel.  Note that
`N` does not occur — it is the fixed activation *fraction* `α` that makes this possible. -/
noncomputable def meanFieldMap (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (α : ℝ)
    (m : S → ℝ) : S → ℝ := fun y =>
  ∑ x, ((m x - activateFraction ν α m x) * P0 x y + activateFraction ν α m x * P1 x y)

/-- The **priority region** of the state `x`: the configurations at which `x` is the marginal
state, the one the budget runs out in.  These `|S|` regions cover the simplex, and the
mean-field map is affine on each of them. -/
def IsPriorityRegion (ν : S → ℝ) (α : ℝ) (m : S → ℝ) (x : S) : Prop :=
  higherPriorityMass ν m x ≤ α ∧ α < higherPriorityMass ν m x + m x

/-- The probability that the **mean-field limiting policy** at the configuration `m` activates
an agent sitting in state `x`: the activated mass in `x` as a fraction of the mass in `x`.
This is the local policy that the index policy converges to, and the one the local chains in
the decomposition are built from. -/
noncomputable def meanFieldActivationProb (ν : S → ℝ) (α : ℝ) (m : S → ℝ) (x : S) : ℝ :=
  if m x = 0 then 0 else activateFraction ν α m x / m x

/-- The mean-field limiting policy as a local policy on `S × Bool`. -/
noncomputable def meanFieldLocalPolicy (ν : S → ℝ) (α : ℝ) (m : S → ℝ)
    (x : S) (a : Bool) : ℝ :=
  if a then meanFieldActivationProb ν α m x else 1 - meanFieldActivationProb ν α m x

/-- One step of the `N`-agent joint state chain under a policy: the agents draw their actions
jointly from `π` and then move independently through their own kernels. -/
noncomputable def rmabStep {N : ℕ} (P0 P1 : Matrix S S ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (s s' : Fin N → S) : ℝ :=
  ∑ a : Fin N → Bool, π s a * ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)

/-- The law of the joint state after `t` steps from a fixed start. -/
noncomputable def rmabLaw {N : ℕ} (P0 P1 : Matrix S S ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (s0 : Fin N → S) : ℕ → (Fin N → S) → ℝ
  | 0, s => if s = s0 then 1 else 0
  | (t + 1), s' => ∑ s, rmabLaw P0 P1 π s0 t s * rmabStep P0 P1 π s s'

/-- The `ℓ¹` norm on configurations, the one the one-step concentration bound is stated in.
The `ℓ∞` bounds reuse `supNorm` from the previous layer, so that they speak the same language
as the uniform global attractor property. -/
noncomputable def l1Norm (v : S → ℝ) : ℝ := ∑ x, |v x|

/-- A plain distribution: nonnegative weights summing to one.  The stationary occupancy of an
index policy vanishes on every non-budgeted action profile, so the strictly positive
`IsPositiveDist` of the two-agent development is unsatisfiable for the chains this theory is
about, and the asymptotic statements use this weaker form.  Every `μ`-weighted quantity
downstream (`muNorm`, `muAgentTVDistN`, `entanglementN`, `IsLocalTransitionN`) is already
stated with products rather than divisions, so nothing needs the weights to be positive. -/
def IsDist {ι : Type*} [Fintype ι] (μ : ι → ℝ) : Prop :=
  (∀ p, 0 ≤ μ p) ∧ ∑ p, μ p = 1

/-- A distribution over joint objects of `N` homogeneous agents is **exchangeable** when it
is invariant under permuting the agents.  The agents of a restless bandit are homogeneous and
the induced chain is symmetric, so its ergodic stationary distribution is exchangeable — and
exchangeability is the exact consequence the asymptotic arguments use: it is what lets a
per-agent quantity be replaced by its average over the agents, turning agent-indexed sums
into configuration-weighted ones.  A reducible chain also has non-exchangeable stationary
distributions concentrated on asymmetric closed classes, which is why the asymptotic
statements carry this as a hypothesis rather than deriving it. -/
def IsExchangeableDist {N : ℕ} {X : Type*} [Fintype X] (μ : (Fin N → X) → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ p : Fin N → X, μ (p ∘ σ) = μ p

/-- **Non-degeneracy in the mean-field limit** (the continuum form of Assumption 2): at
`m✦` some state is served only fractionally — the budget runs out strictly inside it, so the
limiting policy genuinely randomises there.  The strict inequalities place `m✦` in the
interior of its priority region, which is what makes the mean-field map genuinely affine in a
neighbourhood of the fixed point.  The per-`N` form `IsNonDegenerate` of the previous layer
cannot hold at every `N` simultaneously (at `N = 1` the budget floors to `0`), so the
asymptotic statements use this `N`-free form. -/
def IsNonDegenerateMeanField (ν : S → ℝ) (α : ℝ) (mstar : S → ℝ) : Prop :=
  ∃ x : S, 0 < mstar x ∧ 0 < α - higherPriorityMass ν mstar x ∧
    α - higherPriorityMass ν mstar x < mstar x

/-- A matrix is **stable on the tangent space** of the simplex when its powers contract
zero-sum row vectors geometrically.  The affine piece `K` of the mean-field map at the fixed
point is determined by the dynamics only up to the rank-one gauge `K ↦ K + 𝟙 cᵀ` (a constant
row shift, absorbed by the affine offset `b`), and that gauge moves the spectrum; what is
well defined — and what the stability analysis actually uses — is the action of `K` on the
differences `m − m✦`, which sum to zero.  Geometric decay of the powers on that subspace is
the finite-dimensional meaning of "the spectral radius of the linearised dynamics is `< 1`". -/
def IsStableOnTangent (K : Matrix S S ℝ) : Prop :=
  ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ v : S → ℝ, (∑ x, v x) = 0 → ∀ t : ℕ,
      supNorm (Matrix.vecMul v (K ^ t)) ≤ C * ρ ^ t * supNorm v

end MarkovEntanglement


