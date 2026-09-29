-- Prove2me | Definitions.Def_StochasticLinearBandit
-- name    : StochasticLinearBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-29T16:38:38.215736+00:00
-- url     : https://prove2.me/theorems/5866569f-9ecd-4163-b53d-2cd3f801777e
-- statement:
--   The stochastic linear bandit and LinUCB, in two layers.
--
--   DETERMINISTIC (Theorem 19.2 is pathwise): the pseudo-regret (`linearPseudoRegret`)
--
--   $$\hat R_n = \sum_{t=1}^n \langle\theta_*, A^*_t - A_t\rangle,$$
--
--   the confidence ellipsoid of Eq. (19.7) (`confidenceEllipsoid`)
--
--   $$\mathcal{E} = \{\theta : \|\theta - c\|^2_V \le \beta\},$$
--
--   and deterministic-sequence specializations of the Ch 20 estimator/design matrix (`regularizedLeastSquaresSeq`/`regularizedDesignMatrixSeq`, $\Omega := $ `Unit` instances of Mission IX's defs):
--
--   $$\hat\theta_t = V_t(\lambda)^{-1}\sum_{s\le t}x_sa_s \quad\text{and}\quad V_t(\lambda) = \lambda I + \sum_{s\le t}a_sa_s^\top.$$
--
--   Finally, `IsLinUCBTrace` records a run of LinUCB:
--
--   - $\mathcal{C}_t \subseteq \mathcal{E}_t$ (Eq. 19.7);
--   - optimism (Eqs. 19.2/19.3/19.12): $(A_t,\tilde\theta_t) = \mathrm{argmax}_{(a,\theta)\in\mathcal{A}_t\times\mathcal{C}_t}\langle\theta,a\rangle$;
--   - $A^*_t = \mathrm{argmax}_{a\in\mathcal{A}_t}\langle\theta_*,a\rangle$.
--
--   PROBABILISTIC (Cor 19.3/Thm 22.1): a linear bandit with a fixed finite action set `arms : Fin k → Fin d → ℝ` is a `StochasticBandit k` whose arm means are $\langle \mathrm{arms}_j, \theta_*\rangle$ with 1-subgaussian per-arm noise (`IsLinearBandit`); the linear structure enters only through the mean constraint, so the canonical protocol (`BanditPolicy`/`banditMeasure`) is reused unchanged.
-- source:
--   L&S Ch 19.1-19.2, Eqs. (19.5)-(19.7), pp.238-242

import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_StochasticBandit

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 19
(§19.2-§19.3) and Chapter 22.

The stochastic linear bandit and LinUCB. Two layers:

* DETERMINISTIC layer (Theorem 19.2 is pathwise): played actions
  `a : ℕ → Fin d → ℝ`, per-round optimal actions `astar`, the unknown
  parameter `θstar`; the pseudo-regret `R̂_n = ∑_{t=1}^n ⟨θ*, A*_t - A_t⟩`
  (Eq. under §19.2), the confidence ellipsoid `ℰ_t` of Eq. (19.7), and an
  `IsLinUCBTrace` predicate recording that a run of LinUCB (Eqs. (19.2),
  (19.3), (19.7), (19.12)) produced the given sequences. The estimator
  `θ̂_{t-1}` and design matrix `V_{t-1}(λ)` are the Ch 20 objects of
  `Def_SelfNormalizedProcess`, specialized to deterministic sequences
  (`Ω := Unit`); time is `ℕ`-indexed starting at round 1, with sums over
  `s ∈ Finset.range t` using index `s + 1`.

* PROBABILISTIC layer (Corollary 19.3, Theorem 22.1): a stochastic linear
  bandit with a FIXED finite action set `arms : Fin k → Fin d → ℝ` is a
  `StochasticBandit k` whose arm means are `⟨arms j, θ*⟩` — the linear
  structure enters only through this mean constraint, and the canonical
  bandit protocol (`BanditPolicy`/`banditMeasure`) is reused unchanged.
  The noise `η_t = X_t - ⟨θ*, A_t⟩` of Ch 22 is "conditionally
  1-subgaussian given the history"; in the canonical i.i.d.-per-arm model
  the reward given the chosen arm is independent of the past, so per-arm
  1-subgaussian noise (`IsSubgaussianBandit 1`, Mathlib's
  `HasSubgaussianMGF`) is the standard instantiation of that assumption.
-/

open Matrix MeasureTheory ProbabilityTheory NNReal

namespace BanditAlgorithm

/-- `V_t(λ)` for a deterministic action sequence `a_1, a_2, …`: the
regularized design matrix `λ I + ∑_{s=1}^t a_s a_sᵀ` of L&S Eq. (19.6)
(with `V_0 = λ I`), i.e. `regularizedDesignMatrix` at `Ω := Unit`. -/
noncomputable def regularizedDesignMatrixSeq (d : ℕ) (lam : ℝ)
    (a : ℕ → Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  regularizedDesignMatrix d lam (fun s (_ : Unit) ↦ a s) t ()

/-- `θ̂_t` for deterministic action and reward sequences: the `λ`-regularized
least-squares estimator `V_t(λ)⁻¹ ∑_{s=1}^t x_s a_s` of L&S Eq. (19.5),
i.e. `regularizedLeastSquares` at `Ω := Unit`. -/
noncomputable def regularizedLeastSquaresSeq (d : ℕ) (lam : ℝ)
    (a : ℕ → Fin d → ℝ) (x : ℕ → ℝ) (t : ℕ) : Fin d → ℝ :=
  regularizedLeastSquares d lam (fun s (_ : Unit) ↦ a s)
    (fun s (_ : Unit) ↦ x s) t ()

/-- The random pseudo-regret of a linear bandit (L&S §19.2):
`R̂_n = ∑_{t=1}^n ⟨θ*, A*_t - A_t⟩`, where `A*_t` is an optimal action of
round `t` and `A_t` the action played. -/
noncomputable def linearPseudoRegret {d : ℕ} (θstar : Fin d → ℝ)
    (a astar : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, (astar (t + 1) - a (t + 1)) ⬝ᵥ θstar

/-- The confidence ellipsoid `ℰ = {θ : ‖θ - center‖²_V ≤ β}` of L&S
Eq. (19.7), with `‖v‖²_V = v ⬝ᵥ V *ᵥ v`. -/
def confidenceEllipsoid {d : ℕ} (center : Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) : Set (Fin d → ℝ) :=
  {θ | (center - θ) ⬝ᵥ V *ᵥ (center - θ) ≤ β}

/-- A (pathwise) trace of `n` rounds of LinUCB (L&S §19.2-§19.3): action
sets `𝓐_t`, confidence sets `𝓒_t`, radii `β_t`, played actions `a_t`,
optimistic parameters `θ̃_t`, per-round optimal actions `a*_t` and rewards
`x_t`. For every round `t + 1` with `t ∈ range n`:

* Eq. (19.7): `𝓒_{t+1} ⊆ ℰ_{t+1}`, the `β_{t+1}`-ellipsoid centered at the
  regularized least-squares estimate `θ̂_t` in the `V_t(λ)`-norm;
* Eq. (19.12) (optimism): `(a_{t+1}, θ̃_{t+1})` maximizes `⟨θ, b⟩` over
  `𝓐_{t+1} × 𝓒_{t+1}` — equivalently `a_{t+1}` maximizes the upper
  confidence bound `UCB_{t+1}` of Eqs. (19.2)-(19.3);
* `a*_{t+1}` maximizes the true mean reward `⟨θ*, ·⟩` over `𝓐_{t+1}`. -/
def IsLinUCBTrace {d : ℕ} (lam : ℝ) (n : ℕ) (𝓐 𝓒 : ℕ → Set (Fin d → ℝ))
    (β : ℕ → ℝ) (a θtilde astar : ℕ → Fin d → ℝ) (x : ℕ → ℝ)
    (θstar : Fin d → ℝ) : Prop :=
  ∀ t ∈ Finset.range n,
    𝓒 (t + 1) ⊆ confidenceEllipsoid (regularizedLeastSquaresSeq d lam a x t)
        (regularizedDesignMatrixSeq d lam a t) (β (t + 1)) ∧
    a (t + 1) ∈ 𝓐 (t + 1) ∧
    θtilde (t + 1) ∈ 𝓒 (t + 1) ∧
    (∀ b ∈ 𝓐 (t + 1), ∀ θ ∈ 𝓒 (t + 1), b ⬝ᵥ θ ≤ a (t + 1) ⬝ᵥ θtilde (t + 1)) ∧
    astar (t + 1) ∈ 𝓐 (t + 1) ∧
    ∀ b ∈ 𝓐 (t + 1), b ⬝ᵥ θstar ≤ astar (t + 1) ⬝ᵥ θstar

/-- A stochastic linear bandit with the fixed finite action set
`arms : Fin k → Fin d → ℝ` and parameter `θ*` (L&S Ch 22, conditions 1-2):
a `k`-armed stochastic bandit whose arm means are `⟨arms j, θ*⟩` and whose
per-arm centered rewards (the noise `η`) are 1-subgaussian. The linear
structure enters only through the mean constraint, so the canonical bandit
protocol (`BanditPolicy`, `banditMeasure`) applies unchanged. -/
def IsLinearBandit {k d : ℕ} (arms : Fin k → Fin d → ℝ)
    (θstar : Fin d → ℝ) (ν : StochasticBandit k) : Prop :=
  (∀ j, banditArmMean ν j = arms j ⬝ᵥ θstar) ∧ IsSubgaussianBandit 1 ν

end BanditAlgorithm


