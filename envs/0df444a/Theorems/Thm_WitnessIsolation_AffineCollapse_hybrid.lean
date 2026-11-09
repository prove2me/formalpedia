-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_hybrid
-- name    : WitnessIsolation.AffineCollapse.hybrid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:27.048774+00:00
-- url     : https://prove2.me/theorems/ba0a1113-bc28-4445-b272-5757a09e2f9e
-- title:
--   Lemma 3.2 — Hybrid lemma, parts (a) and (b)
-- statement:
--   Let μ and ν be real laws supported respectively on uniquely satisfiable and unsatisfiable descriptions, padded to a common cap ℓ and normalized to v declared variables. Suppose their acceptance gaps are at most ε for every circuit with at most S gates, with 0<ε≤1.
--
--   (a) If S covers fixed-point evaluation at every assignment, then each possible witness x has μ-probability at most ε. For m independent μ draws, the probability of any pair sharing a witness is at most
--
--   $$\binom m2\epsilon.$$
--
--   (b) Let π have an arbitrary probability distribution, let I(π) be its inactive subset of {1,…,m}, and let ρ be an independent tape. Given π, sources are independent, with law ν at inactive positions and μ elsewhere. Write Z=f(π,ρ,E₁,…,E_m) for the Boolean output, and Z′ for the same experiment with all sources drawn from μ. If every restriction obtained by fixing π,ρ and all sources other than an inactive Eᵢ is computed on the union of the two source supports by a circuit of size at most S, then
--
--   $$|\mathbb EZ-\mathbb EZ'|\le\epsilon\max_\pi|I(\pi)|.$$
--
--   Both clauses are retained in one item. This controls collisions without assuming them away and permits replacing inactive sources even when private information has a continuous distribution.
--
--   Only positive-mass values of the other sources need be fixed in this premise. Values of f on zero-mass strings, including malformed descriptions, are unrestricted. An arbitrary independent tape law can also be included in the private data, taking the explicit uniform tape to have length zero.
--
--   Differences from the source:
--   - encoding: normalized descriptions of length at most ℓ and common witness count v → padded input width 2ℓ+1; unique and null source support and minimum fixed-point evaluation cost; reason: actual length and declared dimension are recorded without introducing witness data
--   - encoding: arbitrary private-data distribution and well-defined experiment → arbitrary probability measure with measurable inactive-set map and measurable Boolean slices, and conditional finite sums integrated over it; reason: measurability makes the source expectations meaningful; bounded probabilities ensure integrability without a finite-support restriction
--   - generalization: a size-S circuit for every fixing of the other sources → slice circuits need agree only on the union of the positive-mass supports, for fixings of other sources in that union; reason: the source circuit hypothesis implies this premise; zero-mass strings never contribute to either experiment, so every source instance and its complete conclusion are retained
--   - encoding: draws a tape after the private data and sources → an independent uniform finite tape; any other independent tape law may be absorbed into the arbitrary private-data probability space with explicit tape length zero; reason: conditioning on the augmented private data gives the same source experiment and the same inactive maximum, without restricting the tape law
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Lemma 3.2, printed p. 7, PDF p. 8; proof and standing normalization on printed pp. 7–8, PDF pp. 8–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_probability

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace WitnessIsolation.AffineCollapse

/-- Lemma 3.2, both (a) and (b); slice circuits need agree only on sampled sources. -/
theorem hybrid (ℓ v S : ℕ) (μ ν : Law (Bits (paddedWidth ℓ))) (ε : ℝ)
    (hμ : μ.Supported {E | IsUniqueSource ℓ v E})
    (hν : ν.Supported {E | IsNullSource ℓ v E})
    (hε : 0 < ε ∧ ε ≤ 1) (hind : Indistinguishable μ ν S ε) :
  ((∀ x : Bits v, evaluationCost ℓ v x ≤ (S : ℕ∞)) →
    (∀ x : Bits v, μ.prob (fun E => WitnessRelation ℓ v E x) ≤ ε) ∧
    ∀ m : ℕ,
      sampleExpectation (fun _ : Fin m => μ) (fun E =>
        if ∃ i j : Fin m, i ≠ j ∧ ∃ x, WitnessRelation ℓ v (E i) x ∧
          WitnessRelation ℓ v (E j) x then 1 else 0) ≤ (Nat.choose m 2 : ℝ)*ε) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (η : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure η] (m r : ℕ)
      (I : Ω → Finset (Fin m))
      (f : Ω → Bits r → (Fin m → Bits (paddedWidth ℓ)) → Bool),
    (∀ ρ E, Measurable (fun π => f π ρ E)) →
    Measurable (fun π => I π) →
    (∀ π ρ i, i ∈ I π → ∀ E : Fin m → Bits (paddedWidth ℓ),
      (∀ j, j ≠ i → 0 < μ.mass (E j) ∨ 0 < ν.mass (E j)) →
      ∃ C : Circuit (paddedWidth ℓ) 1, C.size ≤ S ∧
        ∀ e, (0 < μ.mass e ∨ 0 < ν.mass e) →
          C.eval e 0 = f π ρ (Function.update E i e)) →
    |(∫ π, experiment μ ν I f π true ∂η) -
      (∫ π, experiment μ ν I f π false ∂η)| ≤ ε * (inactiveMaximum I : ℝ))
 := by sorry

end WitnessIsolation.AffineCollapse
