-- Prove2me | solution 1 for linear_distance_implies_poly_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:19.844823+00:00
-- url     : https://prove2.me/submissions/dfabc099-82cf-45d6-bbe2-86cb5edeadff

-- Sol generated from Bridges/NeuralCoding/LorentzianDistanceCertificate.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_LorentzianDistanceCertificate
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lorentzian Certificates for Quantum LDPC Code Distance

This file develops a formal framework connecting **quantum LDPC code distance** to
**Lorentzian/log-concave polynomial certificates**. The central insight is that a quantum
code with robust macroscopic distance forces its measurement-profile distribution to
exhibit quantitatively stable Lorentzian geometry, and conversely, collapse of this
geometry signals the existence of low-weight logical operators.

## Main Definitions

* `AdjacentExchange`: Two k-subsets are adjacent if they differ by a single element exchange.
* `boundaryMass`: The mass of the boundary of the support of a distribution μ.
* `layerWeight`: The total mass of μ on subsets of a fixed cardinality k.
* `ExchangeRayleighGap`: A quantitative lower bound on the exchange ratio.
* `GlobalLorentzianGap`: A global Lorentzian gap measuring ultra-log-concavity.
* `DistanceCertificate`: A structure encoding a certified distance witness.
* `computedGapLB`: A computable lower bound on the Lorentzian gap surrogate.

## Main Results

* `expansion_ratio_implies_exchange_gap`: Expansion and ratio control imply a positive
  exchange gap lower bound. (Theorem 1)
* `linear_distance_implies_poly_gap`: Linear code distance forces nonneg global
  Lorentzian gap. (Theorem 2)
* `linear_certified_distance_contrapositive`: Linear certified distance forces
  vanishing of low layers. (Theorem 3)
* `lorentzian_gap_implies_conductance_lb`: Positive Lorentzian gap implies positive
  Hamming conductance — the cross-domain bridge. (Theorem 4)

## Keywords

quantum LDPC, CSS code, code distance certification, Lorentzian polynomial,
strong log-concavity, anti-concentration, Hamming expansion, certificate complexity,
classical witness for quantum quality, expander codes, discrete Hodge theory

## Conjecture (Polynomial Lorentzian certificate for good QLDPC families)

There exist constants C, δ, γ₀ > 0 such that for every sufficiently large member of any
asymptotically good CSS LDPC family with distance at least δn, the associated
measurement-profile surrogate μₙ satisfies lorentzianGap(μₙ) ≥ γ₀ / n^C.
-/


open Finset BigOperators

noncomputable section

/-! ## Section 1: Combinatorial Support Geometry -/




/-! ## Section 2: Lorentzian Gap Surrogate Definitions -/






/-! ## Section 3: Bridge Lemmas -/



/-- If μ vanishes on layers 1..d-1, then layerWeight k = 0 for 0 < k < d. -/
theorem layerWeight_vanish_below_distance {n : ℕ} (μ : Finset (Fin n) → ℝ)
    (d : ℕ) (hdist : ∀ s, 0 < s.card → s.card < d → μ s = 0)
    (k : ℕ) (hk1 : 0 < k) (hk2 : k < d) :
    layerWeight μ k = 0 := by
  unfold layerWeight
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finset.mem_powersetCard] at hs
  exact hdist s (by omega) (by omega)

/-
Minimum mass total bound: if all supported subsets have mass ≥ m and
there are at least N supported subsets, total mass is at least N * m.
-/

/-
Event probability ratio bound from minimum mass and ratio control.
-/

/-! ## Section 4: Main Theorem Suite -/

/-
**Theorem 1: Expansion-to-Lorentzian-gap lower bound.**

If a nonneg distribution μ satisfies positive minimum mass m on its support
and ρ-bounded exchange ratio on adjacent pairs (with full support on all
adjacent pairs), then the exchange Rayleigh gap is at least ρ * m².

This converts expansion/anti-concentration data into a Lorentzian-style exchange
inequality — a new certificate architecture for quantum code quality.
-/


/-
**Theorem 3: Linear certified distance forces vanishing of low layers.**

If μ is a certified distance witness with distance d = n/C, then
layerWeight μ k = 0 for all 0 < k < n/C.
-/

/-
**Theorem 4: Lorentzian gap implies Hamming conductance lower bound.**

A positive exchange Rayleigh gap forces the boundary mass to be positive,
hence the Hamming conductance is positive. This is the cross-domain bridge
from Lorentzian polynomial geometry to Markov chain mixing / graph expansion.

This links algebraic geometry of generating polynomials to Markov-chain
geometry / complexity theory.
-/

/-! ## Section 5: Verified Algorithm -/


/-
The computed gap lower bound is nonneg.
-/


/-! ## Section 6: Additional Bridge Results -/

/-
Layer weights sum to total mass.
-/

/-
A positive global Lorentzian gap implies layer-wise log-concavity.
-/

/-
Exchange gap positive implies total mass positive when there exists
an adjacent exchange pair.
-/


theorem solution    {n : ℕ}
    (μ : Finset (Fin n) → ℝ)
    (C : ℕ)
    (_hC : 0 < C)
    (hcert : IsCertifiedDistanceWitness μ (n / C))
    (_hn : 0 < n)
    (hzero : layerWeight μ 0 = 0)
    (hbridge : ∀ k : ℕ, n / C ≤ k → 1 ≤ k → k + 1 ≤ n →
      layerWeight μ (k - 1) * layerWeight μ (k + 1) ≤ layerWeight μ k ^ 2) :
    ∃ γ : ℝ, γ ≥ 0 ∧ GlobalLorentzianGap μ γ := by
  refine ⟨0, le_refl _, ?_⟩
  intro k hk1 hk2
  simp only [add_zero, one_mul]
  by_cases hkd : n / C ≤ k
  · exact hbridge k hkd hk1 hk2
  · push_neg at hkd
    -- k < n/C, so lw(k) = 0 by the distance condition
    have hk_pos : 0 < k := by omega
    have hlwk : layerWeight μ k = 0 :=
      layerWeight_vanish_below_distance μ _ hcert.2.1 k hk_pos hkd
    -- Also lw(k-1) = 0: either k-1 = 0 (use hzero) or 0 < k-1 < n/C
    have hlwk1 : layerWeight μ (k - 1) = 0 := by
      rcases Nat.eq_or_lt_of_le hk1 with h | h
      · -- k = 1, so k - 1 = 0
        simp [← h, hzero]
      · -- k ≥ 2, so k - 1 ≥ 1 and k - 1 < n/C
        exact layerWeight_vanish_below_distance μ _ hcert.2.1 (k - 1) (by omega) (by omega)
    simp [hlwk, hlwk1]
