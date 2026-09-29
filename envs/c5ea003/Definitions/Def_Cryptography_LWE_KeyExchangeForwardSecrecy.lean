-- Prove2me | Definitions.Def_Cryptography_LWE_KeyExchangeForwardSecrecy
-- name    : Cryptography_LWE_KeyExchangeForwardSecrecy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:00.108177+00:00
-- url     : https://prove2.me/theorems/4300a728-3f3a-463c-af41-8f446e76fc1e
-- title:
--   Aether Catalog definitions — Cryptography_LWE_KeyExchangeForwardSecrecy
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.KeyExchangeForwardSecrecy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/KeyExchangeForwardSecrecy.lean by skeleton subtraction
import Mathlib

/-!
# LWE Key Exchange: Reconciliation, Forward-Secrecy Hybrids, and Parameters

This file isolates three rigorous components of an LWE key-exchange analysis.
It proves a reconciliation margin for bounded accumulated error, gives a finite
probability model in which post-compromise views inherit the usual LWE hybrid
bound, and checks concrete arithmetic for a modulus and dimension commonly
used at the 128-bit design scale.  The final arithmetic theorem is deliberately
stated as a parameter check, not as an unconditional cryptanalytic security
claim.
-/

open Finset BigOperators

noncomputable section

namespace LWEKeyExchange

/-- A probability mass function on a finite set of protocol views. -/
structure FinitePMF (Ω : Type*) [Fintype Ω] where
  /-- Probability assigned to a view. -/
  mass : Ω → ℝ
  /-- Every probability is nonnegative. -/
  nonneg : ∀ x, 0 ≤ mass x
  /-- Probabilities sum to one. -/
  sum_mass : ∑ x, mass x = 1

/-- The `ℓ¹` distance between finite view distributions. -/
def l1Gap {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) : ℝ :=
  ∑ x, |P.mass x - Q.mass x|

/-- The family of post-compromise views, indexed by the exposed static key and
by the challenge session bit. -/
structure PostCompromiseExperiment (Static View : Type*) [Fintype View] where
  /-- Distribution of the complete view after exposure of a static key. -/
  view : Static → Bool → FinitePMF View

/-- Quantitative forward secrecy: exposing any static key leaves the two session
bit experiments within `ε` in `ℓ¹` distance. -/
def ForwardSecure {Static View : Type*} [Fintype View]
    (E : PostCompromiseExperiment Static View) (ε : ℝ) : Prop :=
  ∀ sk, l1Gap (E.view sk false) (E.view sk true) ≤ ε






/-- Concrete dimension used in the checked parameter profile. -/
def concreteDimension : ℕ := 512

/-- Concrete prime modulus used in the checked parameter profile. -/
def concreteModulus : ℕ := 12289

/-- Number of bounded errors accumulated by the concrete reconciliation check. -/
def concreteErrorCount : ℕ := 1024

/-- Per-error integer magnitude used in the concrete reconciliation check. -/
def concreteErrorBound : ℤ := 3





end LWEKeyExchange

end


