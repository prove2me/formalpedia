-- Prove2me | Theorems.Thm_TropicalSheafSampling_tropical_sheaf_reconstruction_perturbation
-- name    : TropicalSheafSampling.tropical_sheaf_reconstruction_perturbation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:57.136759+00:00
-- url     : https://prove2.me/theorems/5cb00880-9de5-4a38-9bdd-e381eb977ddd
-- title:
--   Tropical sheaf reconstruction perturbation
-- statement:
--   Formal statement of `TropicalSheafSampling.tropical_sheaf_reconstruction_perturbation` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalSheafSampling.tropical_sheaf_reconstruction_perturbation    (r₁ r₂ : S →+ O) (rayleigh : S → ℝ) (lam κ ε : ℝ)
--       (_hκε : ε < κ)
--       (hclosed : BandlimitedSubClosed rayleigh lam)
--       (hcond : HasConditionRadius r₁ rayleigh lam κ)
--       (hpert : SheafPerturbationBound r₁ r₂ rayleigh lam ε)
--       (s₁ s₂ : S)
--       (hbl₁ : TropicalBandlimited rayleigh lam s₁)
--       (hbl₂ : TropicalBandlimited rayleigh lam s₂) :
--       (κ - ε) * ‖s₁ - s₂‖ ≤ ‖r₂ s₁ - r₂ s₂‖ + ε * (‖s₁‖ + ‖s₂‖) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalNeuralSheafSampling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalNeuralSheafSampling.lean#L418

-- Thm stub generated from Bridges/TropicalNeuralSheafSampling.lean
import Mathlib
import Definitions.Def_Bridges_TropicalNeuralSheafSampling
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Neural Sheaf Sampling via Idempotent Laplacian Semimodules

This file establishes a formal bridge between tropical/idempotent harmonic analysis
on cellular sheaves and certified sampling/reconstruction theory for machine-learning
sheaf architectures.

## Main Results

* `tropical_sheaf_sampling_injective` — **Theorem A**: Restriction to a sampling set
  satisfying a tropical Poincaré gap is injective on λ-bandlimited sections.
  This is the tropical sheaf analogue of Shannon-Nyquist sampling.

* `tropical_sheaf_bandlimited_reconstruction` — **Theorem B**: Unique existence of
  bandlimited reconstruction from samples in the image of the Paley-Wiener space.

* `tropical_sheaf_reconstruction_stable` — **Theorem C**: Lipschitz stability of
  reconstruction under sample perturbations, with explicit condition-radius bound.

* `tropical_sheaf_reconstruction_perturbation` — **Theorem C'**: Stability under
  perturbation of the sheaf restriction maps themselves.

* `resolvent_iterate_stabilizes` — Iterates of an inflationary monotone resolvent
  operator on a finite partial order converge in finitely many steps.

## Mathematical Context

In classical signal processing, Shannon's sampling theorem states that bandlimited
signals are determined by their samples at a sufficient rate. We establish a tropical
(idempotent/max-plus) analogue for signals valued in cellular sheaves over finite
cell complexes.

The key objects are:
- **Tropical Rayleigh functional**: measures the "spectral energy" of a section
- **Paley-Wiener space PW_λ**: sections with Rayleigh value ≤ λ
- **Certified Poincaré gap**: nonzero sections vanishing on S have energy > λ
- **Condition radius κ**: quantitative lower bound on restriction over PW_λ

## References

- Akian, Gaubert, Kolokoltsov: Idempotent analysis and max-plus algebra
- Hansen, Ghrist: Toward a spectral theory of cellular sheaves
- Cohen, Gaubert, Quadrat: Max-plus algebra and system theory
- Litvinov, Maslov: Idempotent mathematics and mathematical physics

## Keywords

tropical sheaf signal processing, idempotent harmonic analysis, certified sampling,
bandlimited reconstruction, sheaf neural networks, compressed inference,
min-plus spectral theory, residuated operators, topological machine learning
-/

open Function Set

open TropicalSheafSampling

-- ════════════════════════════════════════════════════════════════════════════════
-- PART 1: CORE TROPICAL SHEAF DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════


variable {S : Type*} [AddCommGroup S]
variable {O : Type*} [AddCommGroup O]








-- ════════════════════════════════════════════════════════════════════════════════
-- PART 2: TROPICAL LAPLACIAN AND SPECTRAL STRUCTURES
-- ════════════════════════════════════════════════════════════════════════════════


variable {C₀ C₁ : Type*} [AddCommGroup C₀] [AddCommGroup C₁]





-- ════════════════════════════════════════════════════════════════════════════════
-- PART 3: THEOREM A — TROPICAL SHEAF SAMPLING INJECTIVITY
-- ════════════════════════════════════════════════════════════════════════════════


variable {S : Type*} [AddCommGroup S]
variable {O : Type*} [AddCommGroup O]






-- ════════════════════════════════════════════════════════════════════════════════
-- PART 4: THEOREM B — CERTIFIED BANDLIMITED RECONSTRUCTION
-- ════════════════════════════════════════════════════════════════════════════════


variable {S : Type*} [AddCommGroup S]
variable {O : Type*} [AddCommGroup O]





-- ════════════════════════════════════════════════════════════════════════════════
-- PART 5: MONOTONE ITERATION AND FINITE STABILIZATION
-- ════════════════════════════════════════════════════════════════════════════════


/-
Iterates of an inflationary map form a weakly increasing sequence.
    This models the tropical resolvent iteration: the reconstruction update
    operator is inflationary (each step improves the approximation).
-/

/-
**Finite Stabilization Lemma**: A weakly increasing function `ℕ → α` into
    a finite partial order must eventually become constant.

    This is a fundamental finiteness principle: in a finite poset, ascending
    chains have bounded length. Applied to tropical resolvent iteration,
    it guarantees that the reconstruction process converges in finitely many steps.
-/

/-
**Resolvent Iteration Stabilization**: Iterates of an inflationary monotone
    map on a finite partial order converge to a fixed point in finitely many steps.

    This is the tropical analogue of Bellman iteration convergence: the
    resolvent/update operator is monotone and the state space is finite,
    guaranteeing termination. This theorem connects to `certified_finite_tropical_decomposition`
    from the tropical Choquet closure duality theory.
-/

/-
The stable value of a converged resolvent iteration is a fixed point.
-/


-- ════════════════════════════════════════════════════════════════════════════════
-- PART 6: THEOREM C — STABILITY UNDER PERTURBATIONS
-- ════════════════════════════════════════════════════════════════════════════════


variable {S : Type*} [NormedAddCommGroup S]
variable {O : Type*} [NormedAddCommGroup O]


/-
A positive condition radius implies the Poincaré gap (qualitative from quantitative).
-/

/-
**Theorem C: Tropical Sheaf Reconstruction Stability**

    If the restriction map has condition radius `κ > 0` on PW_λ, then
    reconstruction is Lipschitz stable: two bandlimited sections whose
    restrictions differ by at most `δ` differ by at most `δ/κ`.

    This is the tropical analogue of the Riesz stability bound for
    frame-based reconstruction.
-/

/-
Stability applied to reconstructions of two samples.
-/


-- ════════════════════════════════════════════════════════════════════════════════
-- PART 7: THEOREM C' — SHEAF PERTURBATION STABILITY
-- ════════════════════════════════════════════════════════════════════════════════


variable {S : Type*} [NormedAddCommGroup S]
variable {O : Type*} [NormedAddCommGroup O]


/-
**Theorem C': Sheaf Perturbation Stability**

    If two sheaf restriction maps differ by at most `ε` on PW_λ, and the
    first has condition radius `κ > ε`, then any section that is bandlimited
    and consistent under r₁ is close to any section that is bandlimited
    and consistent under r₂ for the same sample.

    The bound `‖s₁ - s₂‖ ≤ ‖y₁ - y₂‖/(κ - ε) + ε·‖s₂‖/(κ - ε)` captures
    both sample noise and structural perturbation effects.
-/

theorem TropicalSheafSampling.tropical_sheaf_reconstruction_perturbation    (r₁ r₂ : S →+ O) (rayleigh : S → ℝ) (lam κ ε : ℝ)
    (_hκε : ε < κ)
    (hclosed : BandlimitedSubClosed rayleigh lam)
    (hcond : HasConditionRadius r₁ rayleigh lam κ)
    (hpert : SheafPerturbationBound r₁ r₂ rayleigh lam ε)
    (s₁ s₂ : S)
    (hbl₁ : TropicalBandlimited rayleigh lam s₁)
    (hbl₂ : TropicalBandlimited rayleigh lam s₂) :
    (κ - ε) * ‖s₁ - s₂‖ ≤ ‖r₂ s₁ - r₂ s₂‖ + ε * (‖s₁‖ + ‖s₂‖) := by sorry
