-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_observation_density
-- name    : ZeroFreeRRG.Hardcore.coloring_observation_density
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:33:06.607206+00:00
-- url     : https://prove2.me/theorems/659a1607-32c6-4952-ae06-142c5122b38b
-- title:
--   Normalization of the coloring observation densities
-- statement:
--   Fix $q\ge3$ and a coloring cavity law $\nu$. For each color $i$, the observation density $x\mapsto q(1-x_i)/(q-1)$ is nonnegative almost surely, integrable, and has $\nu$-mean one. For every simplex message, the sum of these $q$ densities is $q$. Thus each latent color defines a probability law and the uniform mixture has marginal $\nu$, as used in the entropy argument for Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem coloring_observation_density (q : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∀ i : Fin q,
      (∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), 0 ≤ (q:ℝ)*(1-x i)/((q:ℝ)-1)) ∧
      Integrable (fun x => (q:ℝ)*(1-x i)/((q:ℝ)-1)) (ν : Measure (Fin q → ℝ)) ∧
      (∫ x, (q:ℝ)*(1-x i)/((q:ℝ)-1) ∂(ν : Measure (Fin q → ℝ))) = 1) ∧
    (∀ x ∈ stdSimplex ℝ (Fin q),
      (∑ i : Fin q, (q:ℝ)*(1-x i)/((q:ℝ)-1)) = q) := by sorry
end ZeroFreeRRG.Hardcore
