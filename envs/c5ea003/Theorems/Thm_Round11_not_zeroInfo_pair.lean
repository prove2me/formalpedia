-- Prove2me | Theorems.Thm_Round11_not_zeroInfo_pair
-- name    : Round11.not_zeroInfo_pair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:22:05.822633+00:00
-- url     : https://prove2.me/theorems/f8402252-8138-4616-8370-2e6fd266c896
-- title:
--   A pair of instances separated by both statistics defeats zero information:
-- statement:
--   A pair of instances separated by both statistics defeats zero information:
--   the counting-independence notion is not vacuous.
--
--   ```lean
--   theorem Round11.not_zeroInfo_pair[DecidableEq α] {T : α → β} {S : α → γ} {w₁ w₂ : α}
--       (hne : w₁ ≠ w₂) (hT : T w₁ ≠ T w₂) (hS : S w₁ ≠ S w₂) :
--       ¬ ZeroInfo ({w₁, w₂} : Finset α) T S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Round11FingerprintInformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Round11FingerprintInformation.lean#L234

-- Thm stub generated from Combinatorics/Round11FingerprintInformation.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Definitions.Def_Combinatorics_Round11FingerprintInformation
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

open Round11

open Finset

/-! ## The channel: an exact sum hint is a factorization -/




/-! ## Finitary independence -/

variable {α β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]




/-! ## The truncated fingerprint and the CFSIGMA closure -/

theorem Round11.not_zeroInfo_pair[DecidableEq α] {T : α → β} {S : α → γ} {w₁ w₂ : α}
    (hne : w₁ ≠ w₂) (hT : T w₁ ≠ T w₂) (hS : S w₁ ≠ S w₂) :
    ¬ ZeroInfo ({w₁, w₂} : Finset α) T S := by sorry
