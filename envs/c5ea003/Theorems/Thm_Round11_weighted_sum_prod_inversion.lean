-- Prove2me | Theorems.Thm_Round11_weighted_sum_prod_inversion
-- name    : Round11.weighted_sum_prod_inversion
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:30:17.629691+00:00
-- url     : https://prove2.me/theorems/553cf3e9-e446-4742-af48-4303aedca4ce
-- title:
--   Weighted sum–product inversion.
-- statement:
--   **Weighted sum–product inversion.**  Any *affine* hint `A·p + B·q` together
--   with `N = p·q` pins the factorization down to at most two candidates: a second
--   factorization with the same `N` and the same affine value has `p = p'`, or else
--   `A·p·p' = B·N`, which determines `p'` from `p`.
--
--   This is what makes the GROUPOID identity of Part II a *channel*: rewriting
--   `C·n = n + (p-1)(n/d_p) + (q-1)(n/d_q) + (p-1)(q-1)` with `(p-1)(q-1) = N-p-q+1`
--   turns the orbit count into the affine observation
--   `(n/d_p - 1)·p + (n/d_q - 1)·q = C·n - n - n/d_p - n/d_q - N - 1`.
--   In the balanced case `d_p = d_q` both coefficients vanish — the observation is
--   empty, which is exactly `Round11.groupoid_balanced_no_leak`.
--
--   ```lean
--   theorem Round11.weighted_sum_prod_inversion{A B p q p' q' N : ℕ}
--       (h : p * q = N) (h' : p' * q' = N) (hlin : A * p + B * q = A * p' + B * q') :
--       p = p' ∨ A * p * p' = B * N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Round11FingerprintInformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Round11FingerprintInformation.lean#L53

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

theorem Round11.weighted_sum_prod_inversion{A B p q p' q' N : ℕ}
    (h : p * q = N) (h' : p' * q' = N) (hlin : A * p + B * q = A * p' + B * q') :
    p = p' ∨ A * p * p' = B * N := by sorry
