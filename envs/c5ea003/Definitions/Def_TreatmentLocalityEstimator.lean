-- Prove2me | Definitions.Def_TreatmentLocalityEstimator
-- name    : TreatmentLocalityEstimator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T16:00:24.503819+00:00
-- url     : https://prove2.me/theorems/ad5262a5-9883-4056-94e6-6ff2bc946133
-- title:
--   A/B vs. information-sharing statistics, differentiable estimators, and asymptotic covariance matrices
-- statement:
--   The per-step statistics of the two data-processing schemes of arXiv:2407.19618 and the covariance objects of its asymptotic theory. For a sample $X_i = (s_i, \gamma_i, s_{i+1}, r_i)$, the raw statistics of arm $a$ are the indicator array $E_{s_i,s_{i+1}}$ and the reward vector $e_{s_i} r_i$; the **AB** scheme weights them by $2\cdot 1[\gamma_i = a]$ (each arm keeps its own samples), and the **IS** scheme by $2\cdot 1[\gamma_i = a, s_i = s^1] + 1[s_i \ne s^1]$ (samples away from the crucial state are shared) — `estObs`. `empAvg` forms the empirical averages $(K^t_\Gamma, R^t_\Gamma, K^c_\Gamma, R^c_\Gamma)$ over $T$ steps: the inputs of a differentiable estimator $\hat\Delta_\Gamma = f(K^t_\Gamma, K^c_\Gamma, R^t_\Gamma, R^c_\Gamma)$ (Definition 1); `meanObs` is their common mean under a step distribution. `EstIdx` flattens the statistic vector into scalar coordinates, and `idxState` reads off the current-state coordinate a statistic is supported on (the coordinates with `idxState` $= s^1$ are those associated with the crucial state). `instCovMatrix` is the instantaneous covariance $\mathrm{Var}_\nu[u_\Gamma(X_1)]$, `lagCovMatrix` the temporal part $\sum_{k\ge 1}\mathrm{Cov}[u_\Gamma(X_1), u_\Gamma(X_{1+k})] + \sum_{k\ge 1}\mathrm{Cov}[u_\Gamma(X_{1+k}), u_\Gamma(X_1)]$, and `asymCovMatrix` their sum $\Sigma_\Gamma$ (Appendix EC.3.2). `mbATE` is the model-based plug-in $\hat P^a(i,j) = K^a(i,j)/\sum_k K^a(i,k)$, $\hat r^a(i) = R^a(i)/\sum_k K^a(i,k)$, $\hat V^a = (I - \gamma\hat P^a)^{-1}\hat r^a$, $\hat\Delta = \hat V^t - \hat V^c$ (Remark 1, Proposition 5), and `mbISCov` is the asymptotic covariance matrix $\Sigma_{IS}$ of the information-sharing model-based estimator, defined as the asymptotic covariance of its linearization at the mean statistics (Theorems 3-4 via Lemma EC.5).
-- source:
--   Chen, Simchi-Levi, Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, https://arxiv.org/abs/2407.19618, §5-§6 (the statistics and Definition 1), Appendix EC.3.2 (the stacked vector u and its covariance decomposition), Remark 1/Proposition 5 (model-based estimators)

import Definitions.Def_TreatmentLocality
import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovChainPathMeasure

/-!
The per-step statistics of the two A/B-testing schemes — plain **A/B testing**
(`AB`, no data sharing) and **information sharing** (`IS`) — their empirical
averages `(K^t_Γ, R^t_Γ, K^c_Γ, R^c_Γ)`, the class of differentiable
estimators `Δ̂_Γ = f(K^t_Γ, K^c_Γ, R^t_Γ, R^c_Γ)`, and the asymptotic
covariance matrices with their instantaneous/lagged decomposition.

Source: Chen, Simchi-Levi, Wang, *Improving the Estimation of Lifetime Effects
in A/B Testing via Treatment Locality* (arXiv:2407.19618):
* §5-§6: the A/B statistics `K^a_AB(Xᵢ) = 2·1[aᵢ = a]·E_{sᵢ,sᵢ₊₁}`,
  `R^a_AB(Xᵢ) = 2·1[aᵢ = a]·e_{sᵢ}rᵢ` and the information-sharing statistics
  `K^a_IS(Xᵢ) = (2·1[aᵢ = a, sᵢ = s¹] + 1[sᵢ ≠ s¹])·E_{sᵢ,sᵢ₊₁}`,
  `R^a_IS(Xᵢ) = (2·1[aᵢ = a, sᵢ = s¹] + 1[sᵢ ≠ s¹])·e_{sᵢ}rᵢ`
  (§6.2), and Definition 1 (differentiable estimators);
* Appendix EC.3.2: the vector `u_Γ(Xᵢ)` stacking the four statistics and its
  asymptotic covariance `Σ_u = Var[u(X₁)] + ∑_{k≥1} Cov[u(X₁), u(X_{1+k})]
  + ∑_{k≥1} Cov[u(X_{1+k}), u(X₁)]`;
* Remark 1 / Proposition 5: the model-based plug-in estimators
  `P̂^a(i,j) = K^a(i,j)/∑_k K^a(i,k)`, `r̂^a(i) = R^a(i)/∑_k K^a(i,k)`,
  `V̂^a = (I - γP̂^a)⁻¹ r̂^a`.

Conventions: an arm `a : Bool` (`true` = treatment); the estimator input space
`EstInput S` assigns to each arm a pair (transition statistic, reward
statistic); the flat coordinate index `EstIdx S` enumerates its scalar
coordinates; `idxState` is the current-state coordinate an index refers to —
the indices with `idxState = s¹` are the coordinates "associated with the
crucial state" in the variance decomposition of Theorem 9.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

/-- The two data-processing schemes of arXiv:2407.19618: plain A/B testing
(`AB`, each arm keeps only its own samples) and information sharing (`IS`,
samples collected away from the crucial state are shared between the arms). -/
inductive Scheme
  | AB
  | IS
deriving DecidableEq

/-- The input of a differentiable estimator: for each arm `a : Bool`, a
transition statistic (an `S × S` array) and a reward statistic (an `S` vector)
— the tuple `(K^t, R^t, K^c, R^c)` of arXiv:2407.19618, Definition 1. -/
abbrev EstInput (S : Type*) : Type _ := Bool → (S → S → ℝ) × (S → ℝ)

variable {S : Type*} [DecidableEq S]

/-- The scheme weight multiplying the raw per-step statistic of arm `a` at the
sample `z`: `2·1[armᵢ = a]` for `AB`; `2·1[armᵢ = a]` at the crucial state and
`1` (shared, both arms) elsewhere for `IS` (arXiv:2407.19618, §5 and §6.2). -/
def schemeWeight (M : Model S) : Scheme → Bool → Step S → ℝ
  | .AB, a, z => 2 * (if z.arm = a then 1 else 0)
  | .IS, a, z => if z.state = M.crucial then 2 * (if z.arm = a then 1 else 0) else 1

/-- The per-step statistic vector `u_Γ(Xᵢ)` of scheme `Γ`: for each arm `a`,
the weighted indicator array `E_{sᵢ,sᵢ₊₁}` (the statistic `K^a_Γ(Xᵢ)`) and the
weighted reward vector `e_{sᵢ}rᵢ` (the statistic `R^a_Γ(Xᵢ)`)
(arXiv:2407.19618, §5, §6.2, Appendix EC.3.2). -/
def estObs (M : Model S) (Γ : Scheme) (z : Step S) : EstInput S :=
  fun a =>
    (fun i j => schemeWeight M Γ a z * (if z.state = i ∧ z.next = j then 1 else 0),
     fun i => schemeWeight M Γ a z * (if z.state = i then z.rwd else 0))

/-- The empirical averages `(K^t_Γ, R^t_Γ, K^c_Γ, R^c_Γ)` over the first `T`
steps of the experiment trajectory `ω`: coordinatewise sample averages of the
per-step statistics `u_Γ(Xᵢ)` (arXiv:2407.19618, §5:
`K^a_Γ = T⁻¹ ∑_{i=1}^T K^a_Γ(Xᵢ)`, and similarly for `R`). -/
noncomputable def empAvg (M : Model S) (Γ : Scheme) (T : ℕ) (ω : ℕ → Step S) :
    EstInput S :=
  fun a =>
    (fun i j => MarkovChainCLT.sampleAvg (fun z => (estObs M Γ z a).1 i j) T ω,
     fun i => MarkovChainCLT.sampleAvg (fun z => (estObs M Γ z a).2 i) T ω)

/-- The flat coordinate index of `EstInput S`: an arm together with either a
transition coordinate `(i, j)` or a reward coordinate `i`. -/
abbrev EstIdx (S : Type*) : Type _ := Bool × (S × S ⊕ S)

/-- The scalar coordinate of an `EstInput` at a flat index. -/
def coordAt (v : EstInput S) : EstIdx S → ℝ
  | (a, .inl (i, j)) => (v a).1 i j
  | (a, .inr i) => (v a).2 i

/-- The current-state coordinate an index refers to: the statistics
`K^a(Xᵢ)(i, j)` and `R^a(Xᵢ)(i)` are supported on the event `sᵢ = i`, so the
coordinates with `idxState = s¹` are exactly the ones "associated with the
crucial state" in the variance decomposition of Theorem 9
(arXiv:2407.19618, Appendix EC.3.2). -/
def idxState : EstIdx S → S
  | (_, .inl (i, _)) => i
  | (_, .inr i) => i

section Chain

variable [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]

/-- The mean statistic vector `E_ν[u_Γ(X)]` under a step distribution `ν` —
the common limit point of the empirical averages of both schemes, at which a
differentiable estimator is differentiated (arXiv:2407.19618, §6.2:
`K^a_Γ → Diag(μ^{1/2})P^a`, `R^a_Γ → Diag(μ^{1/2})r^a` for both `Γ`). -/
noncomputable def meanObs (M : Model S) (Γ : Scheme) (ν : Measure (Step S)) :
    EstInput S :=
  fun a =>
    (fun i j => ∫ z, (estObs M Γ z a).1 i j ∂ν,
     fun i => ∫ z, (estObs M Γ z a).2 i ∂ν)

/-- The instantaneous (lag-`0`) covariance matrix `Var_ν[u_Γ(X₁)]` of the
per-step statistic vector of scheme `Γ` under the stationary step distribution
`ν` — the `Var(u_Γ(X))` term of the variance decomposition in
arXiv:2407.19618, Appendix EC.3.2. -/
noncomputable def instCovMatrix (M : Model S) (Γ : Scheme) (ν : Measure (Step S)) :
    Matrix (EstIdx S) (EstIdx S) ℝ :=
  Matrix.of fun p q =>
    MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => coordAt (estObs M Γ z) p) (fun z => coordAt (estObs M Γ z) q) 0

/-- The lagged (temporal) covariance matrix
`∑_{k≥1} Cov[u_Γ(X₁), u_Γ(X_{1+k})] + ∑_{k≥1} Cov[u_Γ(X_{1+k}), u_Γ(X₁)]` of
scheme `Γ` — the covariance-across-time term `Σ^cov` of Theorem 9
(arXiv:2407.19618, Appendix EC.3.2). -/
noncomputable def lagCovMatrix (M : Model S) (Γ : Scheme) (ν : Measure (Step S)) :
    Matrix (EstIdx S) (EstIdx S) ℝ :=
  Matrix.of fun p q =>
    (∑' k : ℕ, MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => coordAt (estObs M Γ z) p) (fun z => coordAt (estObs M Γ z) q) (k + 1))
    + ∑' k : ℕ, MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => coordAt (estObs M Γ z) q) (fun z => coordAt (estObs M Γ z) p) (k + 1)

/-- The full asymptotic covariance matrix `Σ_Γ` of the statistic vector of
scheme `Γ`: instantaneous part plus lagged part (arXiv:2407.19618,
Appendix EC.3.2, via Lemma EC.4). -/
noncomputable def asymCovMatrix (M : Model S) (Γ : Scheme) (ν : Measure (Step S)) :
    Matrix (EstIdx S) (EstIdx S) ℝ :=
  instCovMatrix M Γ ν + lagCovMatrix M Γ ν

end Chain

section ModelBased

variable [Fintype S]

/-- The model-based plug-in map: from the statistics `v = (K^t, R^t, K^c, R^c)`
form `P̂^a(i,j) = K^a(i,j)/∑_k K^a(i,k)`, `r̂^a(i) = R^a(i)/∑_k K^a(i,k)`, then
`V̂^a = (I - γ P̂^a)⁻¹ r̂^a`, and output the ATE estimate `V̂^t - V̂^c`
(arXiv:2407.19618, Algorithm 1-2, Remark 1 and Proposition 5). -/
noncomputable def mbATE (M : Model S) (v : EstInput S) : S → ℝ :=
  let Vhat : Bool → S → ℝ := fun a =>
    (((1 : Matrix S S ℝ) -
        M.γdisc • Matrix.of fun i j => (v a).1 i j / ∑ k, (v a).1 i k)⁻¹).mulVec
      (fun i => (v a).2 i / ∑ k, (v a).1 i k)
  Vhat true - Vhat false

variable [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]

/-- The asymptotic covariance matrix (indexed by initial states) of the
model-based information-sharing estimator `Δ̂^IS = mbATE ∘ empAvg IS`: the
asymptotic covariance of its linearization at the mean statistic vector — the
matrix `Σ_IS` of arXiv:2407.19618, Theorems 3-4 (via the delta method and the
linearization Lemma EC.5), appearing as the benchmark in the efficiency lower
bound (Theorem 5). -/
noncomputable def mbISCov (M : Model S) (ν : Measure (Step S)) :
    Matrix S S ℝ :=
  Matrix.of fun s s' =>
    MarkovChainCLT.asymptoticCovariance (expKernel M) ν
      (fun z => fderiv ℝ (fun v : EstInput S => mbATE M v s) (meanObs M .IS ν)
        (estObs M .IS z))
      (fun z => fderiv ℝ (fun v : EstInput S => mbATE M v s') (meanObs M .IS ν)
        (estObs M .IS z))

end ModelBased

end TreatmentLocality


