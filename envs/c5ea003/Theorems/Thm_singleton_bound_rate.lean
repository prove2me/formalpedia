-- Prove2me | Theorems.Thm_singleton_bound_rate
-- name    : singleton_bound_rate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:45.261488+00:00
-- url     : https://prove2.me/theorems/e120c6a0-08c1-4b6e-881b-391804696cde
-- title:
--   Singleton bound rate
-- statement:
--   Formal statement of `singleton_bound_rate` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem singleton_bound_rate{len : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
--       (C : Finset (Fin len → α)) (d : ℕ)
--       (hd : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
--       C.card ≤ Fintype.card α ^ (len - (d - 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/TorsionChannelCodes.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/TorsionChannelCodes.lean#L324

-- Thm stub generated from Bridges/NeuralCoding/TorsionChannelCodes.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_TorsionChannelCodes
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Quantum Error Correction via Torsion Channel Codes

This file develops the theory of **prime-channel codes** — error-correcting codes
whose structure arises from the Chinese Remainder Theorem decomposition of cyclic
groups into prime-power components. The key insight is that this decomposition creates
**independent error channels**, one per prime factor, enabling per-channel error
correction analogous to the primewise torsion decomposition of persistence modules.

## Mathematical Context

For coprime m, n, the CRT gives ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ. A codeword over ℤ/mnℤ
decomposes into independent components over each factor. Errors in the m-channel
(changes to the ℤ/mℤ component) don't affect the n-channel, and vice versa.

This mirrors the primewise torsion decomposition in persistence: localization at
prime p extracts the p-primary torsion, and different primes give independent
channels (proved as `prime_channel_independence` in PrimewiseTorsionStability.lean).

## Main Definitions

* `CRTChannelCode` — A code using CRT decomposition for per-channel error correction
* `channelProjection` — Projection of a codeword onto a prime channel
* `channelHammingWeight` — Hamming weight restricted to a single channel
* `TorsionSpectrum` — The torsion spectrum connecting coding theory to persistence

## Main Results

* `crt_channel_projection_additive` — Channel projections are additive group homomorphisms
* `crt_channel_independence` — Errors in one channel don't affect other channels
* `channel_distance_lower_bound` — Minimum distance bound from channel decomposition
* `singleton_error_correction_capacity` — Per-channel error correction theorem
* `torsion_spectrum_refines_hamming` — Cross-domain: torsion spectrum refines Hamming bounds

## References

* Chinese Remainder Theorem codes: cf. Mandelbaum (1976), "On a class of arithmetic codes"
* Primewise torsion stability: `Catalog/Pythagorean/PrimewiseTorsionStability.lean`
* Functorial localization: `Catalog/Pythagorean/FunctorialLocalization.lean`
-/

open Finset BigOperators ZMod

noncomputable section

/-! ## Section 1: CRT Channel Code Infrastructure -/





/-! ## Section 2: Channel Independence -/

/-
**Channel Independence Theorem**: An error that affects only the m-channel
    (i.e., changes the first CRT component) leaves the n-channel unchanged.

    This is the coding-theoretic analog of `prime_channel_independence` from
    PrimewiseTorsionStability.lean: different primes give independent torsion channels.

    The proof proceeds by showing that if two codewords agree on the n-channel,
    then their difference projects to zero on the n-channel.
-/

/-
Converse direction: if two codewords agree on both channels, they are equal.
    This is the **injectivity** of CRT decomposition.
-/

/-! ## Section 3: Channel Hamming Weight and Distance -/




/-
**Channel distance lower bound**: The Hamming weight of a nonzero codeword
    is at least the maximum of its channel weights.

    This means each channel independently contributes to error detection capability.
    The proof uses the fact that if a position has nonzero m-component or nonzero
    n-component, then the full symbol is nonzero (by CRT injectivity).
-/

/-
The n-channel weight is also bounded by the Hamming weight.
-/

/-! ## Section 4: Error Correction via Channel Decomposition -/



/-
**Singleton channel error correction**: If a received word differs from a
    codeword by an m-channel error, the n-channel projection uniquely
    identifies the original codeword among all codewords with distinct n-projections.

    This is the error-correction analog of the primewise stability theorem:
    errors in one channel are invisible to other channels.
-/

/-
**Orthogonality of channel errors**: If an error is simultaneously an
    m-channel error and an n-channel error, then it is no error at all.

    This is the coding-theoretic CRT: independent channels can independently
    detect all errors. Uses by_contra and the CRT bijection.
-/

/-! ## Section 5: Additive Structure of Channel Projections -/

/-
Channel projection on the m-channel is additive (a group homomorphism
    at each coordinate). This is because the CRT map is a ring homomorphism.
-/

/-
The CRT map preserves zero.
-/

/-
The CRT map preserves zero on the n-channel.
-/

/-! ## Section 6: Minimum Distance from Channel Structure -/



/-! ## Section 7: Cross-Domain Bridge — Torsion Persistence to Coding Theory -/



/-
Two distinct primes in a torsion spectrum give coprime channel moduli.
-/


/-! ## Section 8: Hamming Bound via Channel Decomposition -/

/-
**Channel-Refined Singleton Bound**: For a CRT code over ℤ/(m*n)ℤ,
    the code size is bounded by the product of the channel alphabet sizes
    raised to the power (len - d + 1).

    This refines the classical Singleton bound by exploiting the channel structure.
    The proof uses induction on the code length.
-/

/-! ## Section 9: Concrete Example — ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ -/



/-! ## Section 10: Rate-Distance Tradeoff (Conjecture) -/

/-
**Conjecture (Falsifiable)**: For a CRT code over ℤ/(p*q)ℤ of length n
    with minimum distance d, the rate R = log|C|/(n·log(pq)) satisfies
    R ≤ 1 - (d-1)/n.

    This is the channel analog of the Singleton bound. It is testable:
    construct explicit codes and check whether the bound holds.

    Test: For p=2, q=3, n=4, enumerate all possible codes and verify.
-/

theorem singleton_bound_rate{len : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (C : Finset (Fin len → α)) (d : ℕ)
    (hd : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    C.card ≤ Fintype.card α ^ (len - (d - 1)) := by sorry
