-- Prove2me | Theorems.Thm_FreeWitness_SemiprimeWitness_powerSum_recovery
-- name    : FreeWitness.SemiprimeWitness.powerSum_recovery
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:20:25.746523+00:00
-- url     : https://prove2.me/theorems/3c1ebe5f-a22d-4f58-a230-46192a14cc94
-- title:
--   The trace lemma, general (power-weight) form.
-- statement:
--   **The trace lemma, general (power-weight) form.**  If the local weights of the two
--   primes have the shape `x ^ k + c` with `c ≠ 0`, then the aggregate determines the power
--   sum `p ^ k + q ^ k`:
--   `c * (p ^ k + q ^ k) = W (p q) - (p q) ^ k - c ^ 2`.
--
--   Only `c ≠ 0` is used to make the recovery an equality of the *scaled* power sum; see
--   `powerSum_recovery_one` for the (ubiquitous) case `c = 1`.
--
--   ```lean
--   theorem FreeWitness.SemiprimeWitness.powerSum_recovery{k : ℕ} {c : ℤ} {p q : ℕ}
--       (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
--       (hwp : F.w p = (p : ℤ) ^ k + c) (hwq : F.w q = (q : ℤ) ^ k + c) :
--       c * ((p : ℤ) ^ k + (q : ℤ) ^ k) = F.W (p * q) - ((p : ℤ) * q) ^ k - c ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/FreeWitnessTraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/FreeWitnessTraceLemma.lean#L73

-- Thm stub generated from MachineLearning/FreeWitnessTraceLemma.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessTraceLemma
import Definitions.Def_MachineLearning_HalfPlaneClosedForm

/-!
# The CRT-multiplicative free-witness classification: the trace lemma

This file formalises the *abstract skeleton* of the free-witness classification of
`16_FreeWitness_Classification.md`.  The informal claim is:

> a counting aggregate over a CRT-separable domain whose local weights are
> non-polynomial and CRT-multiplicative is a "free witness": it determines the
> factorisation of a semiprime, and it is not a polynomial function of the modulus.

Both halves of that claim are made precise and proved here, in the only regime where
the claim has content, namely semiprimes `N = p q`:

* `SemiprimeWitness` — a value function `W : ℕ → ℤ` on moduli together with a *local
  weight* `w : ℕ → ℤ`, such that `W (p q) = w p * w q` for distinct odd primes.
  This is the "CRT-multiplicative" hypothesis, stripped of any particular model.

* `SemiprimeWitness.powerSum_recovery` — **the trace lemma in its general form.**
  If the local weight has the *power shape* `w x = x ^ k + c` with `c ≠ 0`, then
  `c * (p ^ k + q ^ k) = W (p q) - (p q) ^ k - c ^ 2`.
  The witness value therefore hands over one factor-secret coordinate, the power sum
  `p ^ k + q ^ k`, and nothing else is needed.

* `SemiprimeWitness.trace_recovery` — the case `k = 1`: the *trace* `s = p + q` is
  read off from `W (p q)`.

* `vieta_roots`, `pair_determined_of_sum_prod` — once the trace is known both factors
  are pinned down: they are the roots of `X ^ 2 - s X + N`, and no other pair of
  positive integers has that sum and that product.  This is the "information content
  of every witness is one factor-secret coordinate" statement.

* `not_polynomial_of_not_dvd` — **the polynomial barrier, in sharp form.**  For an
  integer polynomial `P` one always has `a - b ∣ P(a) - P(b)`.  So a single pair of
  moduli `N₁, N₂` with `N₁ - N₂ ∤ W N₁ - W N₂` *proves* that `W` agrees with no
  integer polynomial on any set containing `N₁, N₂`.  This is exactly the proof
  direction sketched in §5 of the paper (a congruence separation), and it is
  unconditional.

* `circleWitness`, `circleCount_not_polynomial` — the classification applied to the
  catalog's modular circle count `HalfPlane.circleCount`.  The local weight is
  `p - χ_p(-1)`; for Blum primes it has power shape `x + 1`, so the trace lemma
  reproves (and generalises) `HalfPlane.sum_of_primes_from_circleCount`, and the
  divisibility criterion shows `C` is not a polynomial in `N`.

Nothing here assumes anything about *how* `W` is computed; the classification is a
statement about the shape of the local weight only.
-/

open FreeWitness

open Finset

/-! ## The abstract witness -/


open SemiprimeWitness

variable (F : SemiprimeWitness)

theorem FreeWitness.SemiprimeWitness.powerSum_recovery{k : ℕ} {c : ℤ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hwp : F.w p = (p : ℤ) ^ k + c) (hwq : F.w q = (q : ℤ) ^ k + c) :
    c * ((p : ℤ) ^ k + (q : ℤ) ^ k) = F.W (p * q) - ((p : ℤ) * q) ^ k - c ^ 2 := by sorry
