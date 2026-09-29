-- Prove2me | Definitions.Def_FedAvg_Model
-- name    : FedAvg_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-22T23:52:38.417069+00:00
-- url     : https://prove2.me/theorems/cd5d9fc5-2abd-4910-a390-081972110766
-- title:
--   Convex FedAvg model and stochastic oracle
-- statement:
--   This definition bundle specifies the objectives, algorithm, oracle, and numerical quantities used by Lemmas 1–2 and Theorem 1. It proves none of those estimates.
--
--   ### Notation and probability model
--   There are $M\ge1$ clients with convex differentiable $L$-smooth functions
--   $F_i:\mathbb R^d\to\mathbb R$, $L>0$, and $F=M^{-1}\sum_iF_i$.
--   Let $x^\star$ minimize $F$, let $x_0$ be deterministic, and let
--   $D=\|x_0-x^\star\|$. The finite-dimensional space permits $d=0$.
--   On a standard Borel probability space $(\Omega,\mathcal A,\mathbb P)$,
--   $\mathcal F_{t\tau+k}$ contains the full history before step $(t,k)$.
--   All $M$ clients participate and use uniform weights. Starting from $x_0$,
--   $x_i^{t,k+1}=x_i^{t,k}-\eta g_i^{t,k}$; each subsequent round starts all
--   clients at the preceding round's terminal average.
--   The states are history-measurable and square integrable; gradients are measurable
--   at the next step and square integrable. Conditional on the current history,
--   client gradients are independent, have means $\nabla F_i(x_i^{t,k})$, and
--   their squared errors have expectations at most $\sigma^2$, with $\sigma\ge0$.
--   The uniform heterogeneity condition is $\|\nabla F_i(x)-\nabla F(x)\|\le\zeta$
--   for every $i,x$, with $\zeta\ge0$.
--   Write $\bar x^{t,k}=M^{-1}\sum_i x_i^{t,k}$,
--   $A_t=\tau^{-1}\sum_{k=1}^{\tau}(F(\bar x^{t,k})-F(x^\star))$, and
--   $A=T^{-1}\sum_{t=0}^{T-1}A_t$. Conditional statements hold almost surely.
--
--   Formalization note: the model makes the source's full-history stochastic-oracle
--   convention explicit. Independence is used in Appendix D.1 immediately after
--   equation (27), PDF p. 87. The moment/measurability and standard Borel conditions
--   are explicit analytic conventions. No convergence or intermediate bound is
--   assumed in the model. The source is Wang et al., *A Field Guide to Federated
--   Optimization*, Section 6.1.1, PDF p. 40, equations (11)–(14), and Section 6.1.2,
--   PDF p. 41, Theorem 1: https://arxiv.org/abs/2107.06917v1.
-- source:
--   Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Theorem 1, equations (15)–(17); Section 6.1.1, PDF p. 40, equations (11)–(14); Appendix D.1, PDF p. 87, equation (27).

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Process.Adapted

/-!
Model for Wang et al., *A Field Guide to Federated Optimization*, arXiv:2107.06917v1,
Section 6.1.1, PDF p. 40, equations (11)--(14). Conditional independence of client
gradients is the oracle convention explicitly used in Appendix D.1, PDF pp. 86--87,
equation (27). All second moments below are genuine integrable random variables.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FedAvg

abbrev ModelSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def objective {d M : ℕ} (f : Fin M → ModelSpace d → ℝ) (x : ModelSpace d) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, f i x

structure Problem (d M : ℕ) where
  clients_pos : 0 < M
  f : Fin M → ModelSpace d → ℝ
  L : ℝ
  σ : ℝ
  ζ : ℝ
  x0 : ModelSpace d
  xstar : ModelSpace d
  smoothness_pos : 0 < L
  noise_nonneg : 0 ≤ σ
  heterogeneity_nonneg : 0 ≤ ζ
  hasGradient : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  smooth : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖
  heterogeneous : ∀ i x, ‖gradient (f i) x - gradient (objective f) x‖ ≤ ζ
  optimal : ∀ x, objective f xstar ≤ objective f x

variable {d M : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Problem d M) (μ : Measure Ω) [IsProbabilityMeasure μ] (τ T : ℕ) (η : ℝ)

/-- A finite FedAvg run. The history index `t * τ + k` counts local stochastic steps. -/
structure Run where
  history : Filtration ℕ mΩ
  x : ℕ → ℕ → Fin M → Ω → ModelSpace d
  g : ℕ → ℕ → Fin M → Ω → ModelSpace d
  x_adapted : ∀ t, t < T → ∀ k, k ≤ τ → ∀ i,
    StronglyMeasurable[history (t * τ + k)] (x t k i)
  x_squareIntegrable : ∀ t, t < T → ∀ k, k ≤ τ → ∀ i, MemLp (x t k i) 2 μ
  g_adapted : ∀ t, t < T → ∀ k, k < τ → ∀ i,
    StronglyMeasurable[history (t * τ + k + 1)] (g t k i)
  g_squareIntegrable : ∀ t, t < T → ∀ k, k < τ → ∀ i, MemLp (g t k i) 2 μ
  unbiased : ∀ t, t < T → ∀ k, k < τ → ∀ i,
    μ[g t k i | history (t * τ + k)] =ᵐ[μ] fun ω ↦ gradient (P.f i) (x t k i ω)
  variance : ∀ t, t < T → ∀ k, k < τ → ∀ i,
    μ[(fun ω ↦ ‖g t k i ω - gradient (P.f i) (x t k i ω)‖ ^ 2) |
      history (t * τ + k)] ≤ᵐ[μ] fun _ ↦ P.σ ^ 2
  independent : ∀ t, t < T → ∀ k, k < τ →
    iCondIndepFun (history (t * τ + k)) (history.le _) (g t k) μ
  initial : ∀ i ω, x 0 0 i ω = P.x0
  local_update : ∀ t, t < T → ∀ k, k < τ → ∀ i,
    x t (k + 1) i =ᵐ[μ] fun ω ↦ x t k i ω - η • g t k i ω
  synchronize : ∀ t, t + 1 < T → ∀ i,
    x (t + 1) 0 i =ᵐ[μ] fun ω ↦ (M : ℝ)⁻¹ • ∑ j, x t τ j ω

variable {P μ τ T η}

def shadow (R : Run P μ τ T η) (t k : ℕ) (ω : Ω) : ModelSpace d :=
  (M : ℝ)⁻¹ • ∑ i, R.x t k i ω

def roundLoss (R : Run P μ τ T η) (t : ℕ) (ω : Ω) : ℝ :=
  (τ : ℝ)⁻¹ * ∑ k ∈ Finset.range τ,
    (objective P.f (shadow R t (k + 1) ω) - objective P.f P.xstar)

def avgLoss (R : Run P μ τ T η) (ω : Ω) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, roundLoss R t ω

def distance (P : Problem d M) : ℝ := ‖P.x0 - P.xstar‖

def shadowDistanceSq (R : Run P μ τ T η) (t k : ℕ) (ω : Ω) : ℝ :=
  ‖shadow R t k ω - P.xstar‖ ^ 2

def clientDriftSq (R : Run P μ τ T η) (t k : ℕ) (i : Fin M) (ω : Ω) : ℝ :=
  ‖R.x t k i ω - shadow R t k ω‖ ^ 2

def progressTerm (R : Run P μ τ T η) (t : ℕ) (ω : Ω) : ℝ :=
  (shadowDistanceSq R t 0 ω - μ[shadowDistanceSq R t τ | R.history (t * τ)] ω) /
    (2 * η * (τ : ℝ))

def deviationTerm (R : Run P μ τ T η) (t : ℕ) (ω : Ω) : ℝ :=
  η * P.σ ^ 2 / (M : ℝ) + P.L / ((M : ℝ) * (τ : ℝ)) *
    ∑ i, ∑ k ∈ Finset.range τ, μ[clientDriftSq R t k i | R.history (t * τ)] ω

def progressRHS (R : Run P μ τ T η) (t : ℕ) (ω : Ω) : ℝ :=
  progressTerm R t ω + deviationTerm R t ω

def driftRHS (P : Problem d M) (τ : ℕ) (η : ℝ) : ℝ :=
  18 * (τ : ℝ) ^ 2 * η ^ 2 * P.ζ ^ 2 + 4 * (τ : ℝ) * η ^ 2 * P.σ ^ 2

def convergenceRHS (P : Problem d M) (τ T : ℕ) (η : ℝ) : ℝ :=
  distance P ^ 2 / (2 * η * (τ : ℝ) * (T : ℝ)) + η * P.σ ^ 2 / (M : ℝ) +
    4 * (τ : ℝ) * η ^ 2 * P.L * P.σ ^ 2 +
    18 * (τ : ℝ) ^ 2 * η ^ 2 * P.L * P.ζ ^ 2

/-- Section 6.1.2, PDF p. 41, equation (16), used only in its nondegenerate regime. -/
def optimizedStep (P : Problem d M) (τ T : ℕ) : ℝ :=
  min (1 / (4 * P.L))
    (min (Real.sqrt (M : ℝ) * distance P /
      (Real.sqrt (τ : ℝ) * Real.sqrt (T : ℝ) * P.σ))
      (min (Real.rpow (distance P) (2 / 3 : ℝ) /
        (Real.rpow (τ : ℝ) (2 / 3 : ℝ) * Real.rpow (T : ℝ) (1 / 3 : ℝ) *
          Real.rpow P.L (1 / 3 : ℝ) * Real.rpow P.σ (2 / 3 : ℝ)))
        (Real.rpow (distance P) (2 / 3 : ℝ) /
          ((τ : ℝ) * Real.rpow (T : ℝ) (1 / 3 : ℝ) *
            Real.rpow P.L (1 / 3 : ℝ) * Real.rpow P.ζ (2 / 3 : ℝ)))))

/-- Section 6.1.2, PDF p. 41, equation (17). -/
def optimizedRHS (P : Problem d M) (τ T : ℕ) : ℝ :=
  2 * P.L * distance P ^ 2 / ((τ : ℝ) * (T : ℝ)) +
    2 * P.σ * distance P / Real.sqrt ((M : ℝ) * (τ : ℝ) * (T : ℝ)) +
    5 * Real.rpow P.L (1 / 3 : ℝ) * Real.rpow P.σ (2 / 3 : ℝ) *
      Real.rpow (distance P) (4 / 3 : ℝ) /
      (Real.rpow (τ : ℝ) (1 / 3 : ℝ) * Real.rpow (T : ℝ) (2 / 3 : ℝ)) +
    19 * Real.rpow P.L (1 / 3 : ℝ) * Real.rpow P.ζ (2 / 3 : ℝ) *
      Real.rpow (distance P) (4 / 3 : ℝ) / Real.rpow (T : ℝ) (2 / 3 : ℝ)

end FedAvg


