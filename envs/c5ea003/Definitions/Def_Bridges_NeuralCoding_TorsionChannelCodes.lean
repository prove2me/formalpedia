-- Prove2me | Definitions.Def_Bridges_NeuralCoding_TorsionChannelCodes
-- name    : Bridges_NeuralCoding_TorsionChannelCodes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:37.867871+00:00
-- url     : https://prove2.me/theorems/4da22cda-91fd-46d6-9857-8f8214d7af2d
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_TorsionChannelCodes
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.TorsionChannelCodes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/TorsionChannelCodes.lean by skeleton subtraction
import Mathlib
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

/-- A **CRT Channel Code** over ℤ/(m*n)ℤ for coprime m, n.
    The code exploits the CRT isomorphism ℤ/(m*n)ℤ ≅ ℤ/mℤ × ℤ/nℤ
    to decompose codewords into two independent channels.
    This is the fundamental new structure connecting coding theory
    to torsion persistence. -/
structure CRTChannelCode (m n len : ℕ) where
  /-- Coprimality assumption -/
  coprime : Nat.Coprime m n
  /-- The code is a set of codewords of length `len` over ℤ/(m*n)ℤ -/
  codewords : Finset (Fin len → ZMod (m * n))
  /-- The code is nonempty -/
  nonempty : codewords.Nonempty

/-- The CRT isomorphism as a ring equivalence. -/
def crtEquiv (m n : ℕ) (h : Nat.Coprime m n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- Project a codeword onto its m-channel (first CRT component). -/
def channelProjectM {m n len : ℕ} (h : Nat.Coprime m n)
    (w : Fin len → ZMod (m * n)) : Fin len → ZMod m :=
  fun i => (crtEquiv m n h (w i)).1

/-- Project a codeword onto its n-channel (second CRT component). -/
def channelProjectN {m n len : ℕ} (h : Nat.Coprime m n)
    (w : Fin len → ZMod (m * n)) : Fin len → ZMod n :=
  fun i => (crtEquiv m n h (w i)).2

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

/-- The **channel Hamming weight** on the m-channel: counts positions where
    the m-component is nonzero. -/
def channelWeightM {m n len : ℕ} [NeZero m] (h : Nat.Coprime m n)
    (w : Fin len → ZMod (m * n)) : ℕ :=
  (Finset.univ.filter fun i => (crtEquiv m n h (w i)).1 ≠ 0).card

/-- The **channel Hamming weight** on the n-channel. -/
def channelWeightN {m n len : ℕ} [NeZero n] (h : Nat.Coprime m n)
    (w : Fin len → ZMod (m * n)) : ℕ :=
  (Finset.univ.filter fun i => (crtEquiv m n h (w i)).2 ≠ 0).card

/-- The Hamming weight of a word over ℤ/(m*n)ℤ. -/
def hammingWeightMN {m n len : ℕ} [NeZero (m * n)]
    (w : Fin len → ZMod (m * n)) : ℕ :=
  (Finset.univ.filter fun i => w i ≠ 0).card

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

/-- An **m-channel error** is a perturbation that only affects the m-component.
    Formally: w₁ and w₂ differ, but their n-projections agree. -/
def IsMChannelError {m n len : ℕ} (h : Nat.Coprime m n)
    (w₁ w₂ : Fin len → ZMod (m * n)) : Prop :=
  channelProjectN h w₁ = channelProjectN h w₂

/-- An **n-channel error** is a perturbation that only affects the n-component. -/
def IsNChannelError {m n len : ℕ} (h : Nat.Coprime m n)
    (w₁ w₂ : Fin len → ZMod (m * n)) : Prop :=
  channelProjectM h w₁ = channelProjectM h w₂

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

/-- A **TorsionSpectrum** captures the prime decomposition of torsion in a
    finitely generated abelian group, bridging persistence theory and coding theory.

    In persistence: each prime p contributes a p-primary torsion channel.
    In coding: each prime p contributes an independent error-correction channel.
    The spectrum records which primes appear and with what multiplicity. -/
structure TorsionSpectrum where
  /-- The set of primes contributing torsion -/
  primes : Finset ℕ
  /-- All entries are prime -/
  all_prime : ∀ p ∈ primes, Nat.Prime p
  /-- Multiplicity of each prime -/
  multiplicity : ℕ → ℕ


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

/-! ## Section 11: Syndrome Decoding via CRT -/

/-- The **syndrome** of a word with respect to a codeword on the m-channel.
    This is the difference of channel projections. -/
def syndromM {m n len : ℕ} (h : Nat.Coprime m n)
    (received codeword : Fin len → ZMod (m * n)) : Fin len → ZMod m :=
  fun i => channelProjectM h received i - channelProjectM h codeword i

/-- The **syndrome** on the n-channel. -/
def syndromN {m n len : ℕ} (h : Nat.Coprime m n)
    (received codeword : Fin len → ZMod (m * n)) : Fin len → ZMod n :=
  fun i => channelProjectN h received i - channelProjectN h codeword i

/-
**Syndrome uniqueness**: Two received words with the same syndrome
    on both channels must be the same word. Uses CRT injectivity.
-/

/-! ## Section 12: Interleaving Stability Connection -/

/-
**Interleaving-Distance Bridge**: If two codewords are close in Hamming
    distance, their channel projections are also close.

    This connects the interleaving stability bound from persistence theory
    (the δ-interleaving distance between persistence modules) to the
    minimum distance of the CRT channel code.

    The proof shows that projection cannot increase Hamming distance.
-/

/-
Projection onto the n-channel is also non-expansive.
-/

/-! ## Section 13: Full CRT Decomposition for Multiple Primes -/

/-
For three pairwise coprime moduli, the CRT decomposes into three channels.
-/

/-
**Unique N-Channel Decoding**: If two codewords share the same n-channel
    projection AND the same m-channel projection, they must be the same codeword.
    This means the pair (m-projection, n-projection) uniquely identifies codewords.

    Combined with `m_channel_error_invisible_to_n`, this gives a decoding strategy:
    use the error-free channel to narrow candidates, then the other channel to decode.
    Uses by_contra and CRT injectivity.
-/

/-
**Hamming distance decomposition via CRT channels**: The Hamming distance
    between two codewords is at least the Hamming distance of their m-channel
    projections. Combined with `channel_projection_n_nonexpansive`, this means
    the full distance dominates each channel distance.

    This is the key structural result: channel distances provide independent
    lower bounds on the code's minimum distance.
-/

/-! ## Axiom verification -/

end


