-- Prove2me | Theorems.Thm_BanditAlgorithm_sample_complexity_from_witness_bounds
-- name    : BanditAlgorithm.sample_complexity_from_witness_bounds
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:20:21.180542+00:00
-- url     : https://prove2.me/theorems/affeaa52-ae2c-4ea9-befb-860624d21853
-- title:
--   Sample complexity from an integrable witness time
-- statement:
--   Suppose that for every $\varepsilon>0$ there is a random time $W_\varepsilon$ with $\mathbb E[W_\varepsilon]<\infty$, not depending on $\delta$, such that for every $\delta\in(0,1)$,
--   $$\tau_\delta\ \le\ W_\varepsilon+\left\lceil(1+\varepsilon)\,c\,\log\tfrac1\delta\right\rceil\quad\text{almost surely.}$$
--   Then $\mathbb E[\tau_\delta]<\infty$ at every confidence level, and for every $\varepsilon>0$,
--   $$\frac{\mathbb E[\tau_\delta]}{\log(1/\delta)}\ \le\ c+\varepsilon\qquad\text{for all }\delta\text{ small enough.}$$
--
--   This is the bookkeeping that turns the finite-$\delta$ bounds of Garivier & Kaufmann's Theorem 14 into the limit statement of Lattimore--Szepesv\'ari's Theorem 33.6, and it explains where the $\varepsilon$ of Theorem 14 has to sit. Once $\varepsilon$ is fixed, $\mathbb E[W_\varepsilon]$ is a constant and is divided away by $\log(1/\delta)\to\infty$; the multiplicative constant $(1+\varepsilon)c$ is not. So the bound must be sharp in its multiplicative constant and may be arbitrarily lossy in the additive one --- which is precisely the trade the crossing estimate makes.
--
--   Stated for an abstract family of $\overline{\mathbb N}$-valued times, so it applies to any stopping rule with a bound of this shape.
-- source:
--   The passage from Garivier & Kaufmann, COLT 2016, Theorem 14 to the limit form of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 33.6, p. 410.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal Filter Topology

theorem BanditAlgorithm.sample_complexity_from_witness_bounds {k : ℕ} [NeZero k]
    {P : MeasureTheory.Measure (ℕ → Fin k × ℝ)} [MeasureTheory.IsProbabilityMeasure P]
    {τ : ℝ → (ℕ → Fin k × ℝ) → ℕ∞} {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ ε : ℝ, 0 < ε → ∃ W : (ℕ → Fin k × ℝ) → ℕ,
      (∫⁻ ω, (W ω : ℝ≥0∞) ∂P ≠ ⊤) ∧
        ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
          τ δ ω ≤ ((W ω : ℕ∞) + ((⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞))) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂P ≠ ⊤) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂P).toReal / Real.log (1 / δ) ≤ c + ε := by
  sorry
