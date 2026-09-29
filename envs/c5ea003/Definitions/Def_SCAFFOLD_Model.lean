-- Prove2me | Definitions.Def_SCAFFOLD_Model
-- name    : SCAFFOLD_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-23T05:35:11.943677+00:00
-- url     : https://prove2.me/theorems/5f6355f8-9342-497f-8aa5-f88eb206cd60
-- title:
--   SCAFFOLD objectives, option II updates, oracle, and output statistics
-- statement:
--   Formalization note: a source-backed definition bundle for actual option II algorithm runs and output statistics, with explicit stochastic-oracle conventions. It asserts no convergence theorem.
--
--   ### Notation and probability model
--   There are $N\ge1$ clients, a model space $\mathbb R^d$ (including $d=0$),
--   differentiable client losses $f_i$ with $\beta$-Lipschitz gradients, $\beta>0$,
--   and $f=N^{-1}\sum_i f_i$. The starting point $x^0$ is deterministic and
--   $\sigma\ge0$ bounds within-client stochastic-gradient standard deviation.
--   A run has $T\ge1$ rounds, $K\ge1$ local steps, $1\le S\le N$ clients per round,
--   local step $\eta_l>0$, global step $\eta_g\ge1$, and $h=K\eta_l\eta_g$.
--   All random variables live on a standard Borel probability space $(\Omega,\mathcal A,\nu)$ with a filtration
--   containing the full history. States and gradient samples are square integrable;
--   gradient samples are conditionally unbiased, have conditional squared error at
--   most $\sigma^2$, and are independent across clients conditional on each step's
--   history. These are explicit fresh-oracle and finite-moment conventions.
--
--   Every round first defines virtual paths for all clients, starting at $y_{i,0}^r=x^r$:
--   $$y_{i,k+1}^r=y_{i,k}^r-\eta_l(g_{i,k}^r-c_i^r+c^r),\qquad
--   c^r=N^{-1}\sum_i c_i^r.$$
--   Then an $S$-element subset is sampled uniformly, conditionally independently of
--   these paths given the past. Equivalently, its conditional distribution given the
--   entire completed virtual-path history is uniform. Only selected clients update
--   their controls to $K^{-1}\sum_{k=0}^{K-1}g_{i,k}^r$; other controls persist.
--   The server update is $x^{r+1}=x^r+(\eta_g/S)\sum_{i\in\mathcal S_r}(y_{i,K}^r-x^r)$.
--   This is option II of Algorithm 1, with the average-gradient form of Appendix E.
--   The model contains the algorithm and oracle laws, not any convergence inequality.
--
--   For convex targets, $x^\star$ minimizes $f$, and the client losses obey
--   $$f_i(y)\ge f_i(x)+\langle\nabla f_i(x),y-x\rangle
--   +\frac\mu2\|y-x\|^2,\qquad \mu\ge0.$$
--   The initial client controls $c_i^0$ are arbitrary deterministic vectors and
--   the server control is their average. Define
--   $$C_0=\frac1N\sum_i\|c_i^0-\nabla f_i(x^\star)\|^2,\qquad
--   V_0=\|x^0-x^\star\|^2+\frac{9Nh^2}{S}C_0.$$
--   For nonconvex targets, $f_{\rm low}\le f(x)$ for all $x$; a minimizer need not
--   exist. Each $c_i^0$ is instead initialized by averaging $K$ fresh stochastic
--   gradients at $x^0$, with the same conditional oracle assumptions. These full-client
--   initialization queries are additional to the $T$ optimization rounds.
--
--   The output is a sampled pre-round server iterate among $x^0,\ldots,x^{T-1}$,
--   represented by its expected loss or squared-gradient statistic. No last-iterate
--   or pathwise guarantee is asserted. Sources: Section 2, PDF p. 2; Algorithm 1,
--   PDF p. 4; Appendix B.1, PDF p. 14, assumptions A3–A5; Appendix E, PDF pp. 25–26,
--   equations (18)–(22), Remark 10; Appendix E.2, PDF pp. 31 and 35, equations
--   (26)–(27) and final warm-start paragraph.
--   Primary reference: Karimireddy et al., *SCAFFOLD: Stochastic Controlled Averaging
--   for Federated Learning*, ICML 2020, https://arxiv.org/abs/1910.06378v4.
-- source:
--   Sai Praneeth Karimireddy, Satyen Kale, Mehryar Mohri, Sashank J. Reddi, Sebastian U. Stich, and Ananda Theertha Suresh, SCAFFOLD: Stochastic Controlled Averaging for Federated Learning, ICML 2020; arXiv:1910.06378v4, https://arxiv.org/abs/1910.06378v4; Section 2, PDF p. 2; Algorithm 1, PDF p. 4; Appendix B.1, PDF p. 14, assumptions A3–A5; Appendix E, PDF pp. 25–26, equations (18)–(22); Appendix E.2, PDF p. 31, equations (26)–(27), and PDF p. 35 final paragraph.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Process.Adapted

/-!
SCAFFOLD option II: Karimireddy et al., arXiv:1910.06378v4, Algorithm 1 (PDF p. 4),
Appendix B.1 (PDF p. 14), Appendix E (PDF pp. 25–26), equations (18)–(22).
The model uses the average-gradient control update, avoiding the sign typo in (19).
Sampling occurs after virtual client trajectories; these trajectories are independent of the
current sampled subset, as stipulated in the paragraph following (22).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SCAFFOLD

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def objective {d N : ℕ} (f : Fin N → Space d → ℝ) (x : Space d) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, f i x

structure Problem (d N : ℕ) where
  clients_pos : 0 < N
  f : Fin N → Space d → ℝ
  β : ℝ
  σ : ℝ
  x0 : Space d
  smoothness_pos : 0 < β
  noise_nonneg : 0 ≤ σ
  hasGradient : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  smooth : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ β * ‖x - y‖

def Convexity {d N : ℕ} (P : Problem d N) (μ : ℝ) : Prop :=
  0 ≤ μ ∧ ∀ i x y, P.f i x + inner ℝ (gradient (P.f i) x) (y - x) +
    μ / 2 * ‖y - x‖ ^ 2 ≤ P.f i y

def IsMinimizer {d N : ℕ} (P : Problem d N) (xstar : Space d) : Prop :=
  ∀ x, objective P.f xstar ≤ objective P.f x

/-- `none` chooses the K-sample warm start; `some c0` fixes deterministic controls. -/
abbrev Initialization (d N : ℕ) := Option (Fin N → Space d)

def roundTime (K r : ℕ) := K + r * (K + 1)

def effectiveStep (K : ℕ) (ηl ηg : ℝ) : ℝ := (K : ℝ) * ηl * ηg

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Problem d N) (ν : Measure Ω) [IsProbabilityMeasure ν]
  (S K T : ℕ) (ηl ηg : ℝ) (init : Initialization d N)

/-- A finite run with fresh conditional stochastic gradients and uniform client sampling.
No descent estimate or convergence conclusion is a field of this structure. -/
structure Run where
  sample_pos : 0 < S
  sample_le : S ≤ N
  steps_pos : 0 < K
  rounds_pos : 0 < T
  history : Filtration ℕ mΩ
  warm : ℕ → Fin N → Ω → Space d
  x : ℕ → Ω → Space d
  c : ℕ → Fin N → Ω → Space d
  y : ℕ → ℕ → Fin N → Ω → Space d
  g : ℕ → ℕ → Fin N → Ω → Space d
  sample : ℕ → Ω → Finset (Fin N)
  warm_adapted : ∀ k, k < K → ∀ i, StronglyMeasurable[history (k + 1)] (warm k i)
  warm_memLp : ∀ k, k < K → ∀ i, MemLp (warm k i) 2 ν
  warm_unbiased : ∀ k, k < K → ∀ i,
    ν[warm k i | history k] =ᵐ[ν] fun _ ↦ gradient (P.f i) P.x0
  warm_variance : ∀ k, k < K → ∀ i,
    ν[(fun ω ↦ ‖warm k i ω - gradient (P.f i) P.x0‖ ^ 2) | history k]
      ≤ᵐ[ν] fun _ ↦ P.σ ^ 2
  warm_independent : ∀ k, k < K → iCondIndepFun (history k) (history.le _) (warm k) ν
  x_adapted : ∀ r, r ≤ T → StronglyMeasurable[history (roundTime K r)] (x r)
  x_memLp : ∀ r, r ≤ T → MemLp (x r) 2 ν
  c_adapted : ∀ r, r ≤ T → ∀ i,
    StronglyMeasurable[history (roundTime K r)] (c r i)
  c_memLp : ∀ r, r ≤ T → ∀ i, MemLp (c r i) 2 ν
  y_adapted : ∀ r, r < T → ∀ k, k ≤ K → ∀ i,
    StronglyMeasurable[history (roundTime K r + k)] (y r k i)
  y_memLp : ∀ r, r < T → ∀ k, k ≤ K → ∀ i, MemLp (y r k i) 2 ν
  g_adapted : ∀ r, r < T → ∀ k, k < K → ∀ i,
    StronglyMeasurable[history (roundTime K r + k + 1)] (g r k i)
  g_memLp : ∀ r, r < T → ∀ k, k < K → ∀ i, MemLp (g r k i) 2 ν
  unbiased : ∀ r, r < T → ∀ k, k < K → ∀ i,
    ν[g r k i | history (roundTime K r + k)] =ᵐ[ν]
      fun ω ↦ gradient (P.f i) (y r k i ω)
  variance : ∀ r, r < T → ∀ k, k < K → ∀ i,
    ν[(fun ω ↦ ‖g r k i ω - gradient (P.f i) (y r k i ω)‖ ^ 2) |
      history (roundTime K r + k)] ≤ᵐ[ν] fun _ ↦ P.σ ^ 2
  independent : ∀ r, r < T → ∀ k, k < K →
    iCondIndepFun (history (roundTime K r + k)) (history.le _) (g r k) ν
  sample_card : ∀ r, r < T → ∀ᵐ ω ∂ν, (sample r ω).card = S
  sample_adapted : ∀ r, r < T → ∀ A : Finset (Fin N),
    StronglyMeasurable[history (roundTime K (r + 1))]
      (fun ω ↦ if sample r ω = A then (1 : ℝ) else 0)
  sample_uniform : ∀ r, r < T → ∀ A : Finset (Fin N),
    ν[(fun ω ↦ if sample r ω = A then (1 : ℝ) else 0) |
      history (roundTime K r + K)] =ᵐ[ν]
        fun _ ↦ if A.card = S then (Nat.choose N S : ℝ)⁻¹ else 0
  initial_x : x 0 =ᵐ[ν] fun _ ↦ P.x0
  initial_c : ∀ i, c 0 i =ᵐ[ν] fun ω ↦
    match init with
    | some c0 => c0 i
    | none => (K : ℝ)⁻¹ • ∑ k ∈ Finset.range K, warm k i ω
  start : ∀ r, r < T → ∀ i, y r 0 i =ᵐ[ν] x r
  local_update : ∀ r, r < T → ∀ k, k < K → ∀ i,
    y r (k + 1) i =ᵐ[ν] fun ω ↦ y r k i ω -
      ηl • (g r k i ω - c r i ω + (N : ℝ)⁻¹ • ∑ j, c r j ω)
  control_update : ∀ r, r < T → ∀ i,
    c (r + 1) i =ᵐ[ν] fun ω ↦ if i ∈ sample r ω then
      (K : ℝ)⁻¹ • ∑ k ∈ Finset.range K, g r k i ω else c r i ω
  server_update : ∀ r, r < T → x (r + 1) =ᵐ[ν] fun ω ↦
    x r ω + (ηg / (S : ℝ)) • ∑ i ∈ sample r ω, (y r K i ω - x r ω)

variable {P ν S K T ηl ηg init}

def initialControlError (P : Problem d N) (c0 : Fin N → Space d) (xstar : Space d) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ‖c0 i - gradient (P.f i) xstar‖ ^ 2

def initialPotential (P : Problem d N) (S : ℕ) (h : ℝ)
    (c0 : Fin N → Space d) (xstar : Space d) : ℝ :=
  ‖P.x0 - xstar‖ ^ 2 + 9 * (N : ℝ) * h ^ 2 / (S : ℝ) *
    initialControlError P c0 xstar

def weight (μ h : ℝ) (r : ℕ) : ℝ := (1 - μ * h / 2)⁻¹ ^ (r + 1)

def weightSum (μ h : ℝ) (T : ℕ) : ℝ := ∑ r ∈ Finset.range T, weight μ h r

def expectedGap (A : Run P ν S K T ηl ηg init) (xstar : Space d) (r : ℕ) : ℝ :=
  ∫ ω, objective P.f (A.x r ω) - objective P.f xstar ∂ν

def weightedGap (A : Run P ν S K T ηl ηg init) (xstar : Space d) (μ : ℝ) : ℝ :=
  (weightSum μ (effectiveStep K ηl ηg) T)⁻¹ * ∑ r ∈ Finset.range T,
    weight μ (effectiveStep K ηl ηg) r * expectedGap A xstar r

def averageGradientSq (A : Run P ν S K T ηl ηg init) : ℝ :=
  (T : ℝ)⁻¹ * ∑ r ∈ Finset.range T,
    ∫ ω, ‖gradient (objective P.f) (A.x r ω)‖ ^ 2 ∂ν

def convexRHS (P : Problem d N) (S K T : ℕ) (ηl ηg μ : ℝ)
    (c0 : Fin N → Space d) (xstar : Space d) : ℝ :=
  let h := effectiveStep K ηl ηg
  initialPotential P S h c0 xstar / (h * weightSum μ h T) +
    12 * h * P.σ ^ 2 / ((K : ℝ) * (S : ℝ)) * (1 + (S : ℝ) / ηg ^ 2)

def nonconvexRHS (P : Problem d N) (S K T : ℕ) (ηl ηg fLower : ℝ) : ℝ :=
  let h := effectiveStep K ηl ηg
  14 * (objective P.f P.x0 - fLower) / (h * (T : ℝ)) +
    70 * P.β * h * P.σ ^ 2 / ((K : ℝ) * (S : ℝ)) * (1 + (S : ℝ) / ηg ^ 2)

end SCAFFOLD


