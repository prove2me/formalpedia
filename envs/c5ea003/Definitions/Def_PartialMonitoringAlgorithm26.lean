-- Prove2me | Definitions.Def_PartialMonitoringAlgorithm26
-- name    : PartialMonitoringAlgorithm26
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-05T20:18:17.6126+00:00
-- url     : https://prove2.me/theorems/c2dbf7ba-17ac-428a-beff-d9a436d5c200
-- title:
--   Algorithm 26 vector estimators and exploration–stability objective
-- statement:
--   This interface packages the optimization objects used by the exponential-weights partial-monitoring policy of Algorithm 26.
--
--   For a finite comparator set $S$, a vector estimator $f(a,\sigma)_b$ vanishes outside $S$ and estimates every loss coordinate in $S$ up to a common outcome-dependent additive shift:
--
--   $$
--   \sum_a f(a,\Phi_{ai})_b=L_{bi}+c_i.
--   $$
--
--   The stability function is
--
--   $$
--   \Psi_q(z)=\langle q,e^{-z}+z-1\rangle.
--   $$
--
--   For a learning rate $\eta$, reference distribution $q$, sampling distribution $p$ in the relative interior of the simplex, estimator $f$, and outcome $i$, the Algorithm 26 objective is
--
--   $$
--   \frac{(p-q)^\top L e_i}{\eta}
--   +\frac1{\eta^2}\sum_a p_a\Psi_q\!\left(\frac{\eta f(a,\Phi_{ai})}{p_a}\right).
--   $$
--
--   The bundle also records simplex-interiority and support predicates used by equations (37.12)–(37.13).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), §37.5, printed pp. 492–494, equations (37.12)–(37.14), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Exp


open scoped BigOperators

namespace BanditAlgorithm

variable {k d : ℕ} {𝕊 : Type*}

/-- The book's vector loss-estimator class `E^vec`, parameterized by the
finite set `S` of comparator actions on which exponential weights runs. -/
def PMVectorEstimatorOn (G : PartialMonitoringGame k d 𝕊)
    (S : Finset (Fin k)) (f : Fin k → 𝕊 → Fin k → ℝ) : Prop :=
  (∀ a σ b, b ∉ S → f a σ b = 0) ∧
  ∀ i : Fin d, ∃ c : ℝ, ∀ b ∈ S,
    ∑ a : Fin k, f a (G.Φ a i) b = G.L b i + c

/-- The exact exponential-weights stability function
`Psi_q(z) = <q, exp(-z) + z - 1>`. -/
noncomputable def pmPsi (q z : Fin k → ℝ) : ℝ :=
  ∑ b : Fin k, q b * (Real.exp (-z b) + z b - 1)

/-- A probability vector in the relative interior of the finite simplex. -/
def PMInteriorDistribution (p : Fin k → ℝ) : Prop :=
  p ∈ stdSimplex ℝ (Fin k) ∧ ∀ a, 0 < p a

/-- `q` is supported on the comparator set `S`. -/
def PMSupportedOn (S : Finset (Fin k)) (q : Fin k → ℝ) : Prop :=
  q ∈ stdSimplex ℝ (Fin k) ∧ ∀ a, a ∉ S → q a = 0

/-- The exploration--stability objective inside Eq. (37.12), for one
outcome `i`. -/
noncomputable def pmAlgorithm26Objective
    (G : PartialMonitoringGame k d 𝕊) (η : ℝ)
    (q p : Fin k → ℝ) (f : Fin k → 𝕊 → Fin k → ℝ)
    (i : Fin d) : ℝ :=
  (1 / η) * ∑ a : Fin k, (p a - q a) * G.L a i +
    (1 / η ^ 2) * ∑ a : Fin k, p a *
      pmPsi q (fun b => η * f a (G.Φ a i) b / p a)

end BanditAlgorithm


