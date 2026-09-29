-- Prove2me | Definitions.Def_Combinatorics_Round11FingerprintInformation
-- name    : Combinatorics_Round11FingerprintInformation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:34:08.43126+00:00
-- url     : https://prove2.me/theorems/f660111d-7950-4af2-868f-219a230c5bad
-- title:
--   Aether Catalog definitions — Combinatorics_Round11FingerprintInformation
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Round11FingerprintInformation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Round11FingerprintInformation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
/-
# Round-11 Closures, Part III: CFSIGMA — the hint feed is starved

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypothesis **CFSIGMA**).

The paper's central claim is that the Coppersmith hint-amplification channel
*exists* — an approximation `σ̂ ≈ p + q` is worth a factorization — but that the
cycle-index fingerprint provides *no source* for it: below the order scale the
fingerprint carries zero mutual information with `(p+q) mod ℓ`.

This file proves both halves in an exact, finitary form.

* **The channel exists.**  `Round11.sum_prod_inversion`: the pair `(p+q, p·q)`
  determines `{p, q}`.  An *exact* hint `σ = p + q` is literally a factorization.
* **The source is starved.**  We use the finitary (counting) notion of
  independence `Round11.ZeroInfo`: a statistic `T` is uninformative about a
  secret `S` on a finite instance set `Ω` when every joint fibre has exactly the
  product cardinality.  `Round11.cfsigma_starved` shows that the *truncated
  fingerprint* `c ↦ F(c)`, `1 ≤ c ≤ D`, restricted to instances whose two
  multiplicative orders exceed `D`, is uninformative about `(p+q) mod ℓ` — for
  **every** modulus `ℓ` and **every** instance set.  By the data-processing
  lemma `Round11.zeroInfo_comp`, no post-processing of the truncated fingerprint
  can do better (`Round11.cfsigma_starved_postprocessed`).

The proof of starvation is Part I's order seal: below the order scale the
fingerprint is a *constant* function of the instance, so its fibres are either
empty or all of `Ω`.  Non-vacuity of the hypothesis is witnessed by
`Round11.cfsigma_instance_witness`.
-/

namespace Round11

open Finset

/-! ## The channel: an exact sum hint is a factorization -/




/-! ## Finitary independence -/

variable {α β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-- `ZeroInfo Ω T S` : on the finite instance set `Ω`, the statistic `T` carries
zero information about the secret `S`, in the exact counting sense that every
joint fibre has product cardinality (equivalently, the empirical distributions of
`T` and `S` on `Ω` are independent). -/
def ZeroInfo (Ω : Finset α) (T : α → β) (S : α → γ) : Prop :=
  ∀ t s, (Ω.filter (fun w => T w = t ∧ S w = s)).card * Ω.card
      = (Ω.filter (fun w => T w = t)).card * (Ω.filter (fun w => S w = s)).card



/-! ## The truncated fingerprint and the CFSIGMA closure -/

/-- An instance is a triple `(p, q, b)`. -/
abbrev Instance := ℕ × ℕ × ℕ

/-- The fingerprint truncated to the window `1 ≤ c ≤ D`: this is everything an
attacker can read off the cycle-index object in `poly(log N)` time per
coefficient, before the order scale is reached. -/
def truncFinger (D : ℕ) (I : Instance) : Fin D → ℕ :=
  fun c => fpr I.2.2 (I.1 * I.2.1) ((c : ℕ) + 1)

/-- The secret statistic of CFSIGMA: `(p+q) mod ℓ`. -/
def sigmaMod (l : ℕ) (I : Instance) : ℕ := (I.1 + I.2.1) % l




/-- The window `1 ≤ d ≤ D` of the `N`-computable Möbius coefficients `M_d` — the
per-coefficient cycle-index object of CIFINGER. -/
def truncMob (D : ℕ) (I : Instance) : Fin D → ℤ :=
  fun d => mobRaw I.2.2 (I.1 * I.2.1) ((d : ℕ) + 1)




/-! ## Non-vacuity -/





end Round11


