-- Prove2me | Theorems.Thm_BettiWhittaker_Sign_triangular_odd_iff
-- name    : BettiWhittaker.Sign.triangular_odd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:45.366987+00:00
-- url     : https://prove2.me/theorems/e90b0303-eba6-44df-ba9d-4ee0c09c8677
-- title:
--   The complex (triangular) contribution `n(n-1)/2` is odd iff `n ≡ 2` or `3 (mod 4)`.
-- statement:
--   The complex (triangular) contribution `n(n-1)/2` is odd **iff** `n ≡ 2` or `3 (mod 4)`.
--
--   ```lean
--   theorem BettiWhittaker.Sign.triangular_odd_iff(n : ℕ) :
--       (n * (n - 1) / 2) % 2 = 1 ↔ (n % 4 = 2 ∨ n % 4 = 3) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BettiWhittaker/BottomDegreeParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BettiWhittaker/BottomDegreeParity.lean#L91

-- Thm stub generated from Applications/BettiWhittaker/BottomDegreeParity.lean
import Mathlib
import Definitions.Def_Applications_BettiWhittaker_BottomDegreeParity
/-
# The contragredient sign `(-1)^{b(F,n)}` and its dependence on `n mod 4`

This file analyses the **explicit integer sign** appearing in the Betti–Whittaker contragredient
period relation for `GL(n)` over a number field `F` with `r₁` real and `r₂` complex places
(see `NumberTheory/BettiWhittakerContragredientFormal.lean` for the structural period statement):

  `p^b(π∨) = (-1)^{b(F,n)} · p^b(π)`,    where    `b(F,n) = r₁·⌊n²/4⌋ + r₂·n(n-1)/2`.

That companion file states the relation with an abstract quadratic character `ε(disc k)^{b(F,n)}`.
Here we compute the *concrete* sign `(-1)^{b(F,n)}` and prove that it depends on `n`
**only through `n mod 4`**:

* `n ≡ 0, 1 (mod 4)` : the sign is `+1` for **every** number field — the period is
  contragredient-invariant;
* `n ≡ 3 (mod 4)`    : the sign is `(-1)^{r₂}`, depending **only on the number of complex
  places** (the real places drop out);
* `n ≡ 2 (mod 4)`    : the sign is `(-1)^{r₁ + r₂}`.

The mechanism is two parity laws:
  `⌊n²/4⌋` is odd  ⟺  `n ≡ 2 (mod 4)`,
  `n(n-1)/2` is odd ⟺  `n ≡ 2` or `3 (mod 4)`.

This file is self-contained (`import Mathlib`): it re-introduces the bottom degree `bDeg` of the
companion catalog file inside the dedicated namespace `BettiWhittaker.Sign`, and builds the new
sign theory on top of it.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the sign `(-1)^{b(F,n)}` cannot be arbitrary; the floor and triangular
contributions are each periodic mod 4, so the whole sign should be a function of
`(n mod 4, r₁ mod 2, r₂ mod 2)`.  Surprising sub-claim: for `n ≡ 3 (mod 4)` the real places `r₁`
make *no* contribution to the sign.

Experiment (Experimenter): computed `⌊n²/4⌋ mod 2` and `T_{n-1} = n(n-1)/2 mod 2` for `n = 0..11`:
  ⌊n²/4⌋   : 0 0 1 2 4 6 9 12 16 20 25 30  → parity 0 0 1 0 0 0 1 0 0 0 1 0   (odd ⟺ n≡2 mod 4)
  n(n-1)/2 : 0 0 1 3 6 10 15 21 28 36 45 55 → parity 0 0 1 1 0 0  1  1 0 0  1  1 (odd ⟺ n≡2,3 mod 4)
Both confirmed period-4.  Proved both with a `n = 4q+r` decomposition + `interval_cases r`.

Analysis (Analyst): the `n ≡ 3` case is genuinely asymmetric — `⌊n²/4⌋` is even but `T_{n-1}` is
odd, so `b(F,n) ≡ r₂ (mod 2)` and `r₁` cancels.  This asymmetry is invisible from the abstract
`ε(disc)^{b}` statement; it requires the parity computation done here.

Critique (Critic): is the `n ≡ 0,1` invariance vacuous?  No — it holds for ALL fields and strictly
strengthens the period relation by removing the discriminant character entirely.  Adversarial
counterexample hunt: every `(n,r₁,r₂)` with `n ≤ 40, r₁,r₂ ≤ 6` satisfies the characterization
(checked computationally before formalizing); `contraSign_indep_of_real_places_mod4_eq3` records
the most counterintuitive consequence as a theorem rather than a claim.

Synthesis (PI): the boundary is `n mod 4`.  The clean trichotomy is packaged in `contraSign_*`
below, with `contraSign_sq` certifying these are honest square roots of unity.
-/

open scoped BigOperators

open BettiWhittaker.Sign

/-! ## The bottom cohomological degree -/




/-! ## Parity of the two contributions -/

theorem BettiWhittaker.Sign.triangular_odd_iff(n : ℕ) :
    (n * (n - 1) / 2) % 2 = 1 ↔ (n % 4 = 2 ∨ n % 4 = 3) := by sorry
