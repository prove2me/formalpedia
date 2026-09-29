-- Prove2me | Theorems.Thm_FreeWitness_eight_dvd_even_pow_sub_one
-- name    : FreeWitness.eight_dvd_even_pow_sub_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:20:57.623913+00:00
-- url     : https://prove2.me/theorems/6e1790af-c4dc-41de-8bfc-4b046c8f11fd
-- title:
--   `8 ∣ p^{2j} - 1` for odd `p`: the even powers inherit the 2-adic divisibility of the
-- statement:
--   `8 ∣ p^{2j} - 1` for odd `p`: the even powers inherit the 2-adic divisibility of the
--   square (the case `j = 0` being trivial).
--
--   ```lean
--   theorem FreeWitness.eight_dvd_even_pow_sub_one{p : ℕ} (hp : Odd p) (j : ℕ) :
--       (8 : ℤ) ∣ (p : ℤ) ^ (2 * j) - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/FreeWitnessSealing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/FreeWitnessSealing.lean#L55

-- Thm stub generated from MachineLearning/FreeWitnessSealing.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessSigmaK

/-!
# Cycle 3: the sealing question — how much of a witness is a function of `N` alone

§5 of `16_FreeWitness_Classification.md` proposes a proof direction for barrier 4:
*find `N₁ ≡ N₂ (mod 2^k)` with `C(N₁) ≢ C(N₂) (mod 2^k)`; since `p, q mod 2^k` are
underdetermined by `N mod 2^k`, such a pair would prove that no formula in the residues
of `N` exists.*

The computations behind this file show that the situation is more delicate than the
paper assumes, and both halves are proved here.

**Negative result (the truncation leaks nothing, up to 6 bits).**
`sigma_even_two_adic`: for *every* even exponent `2j` and all distinct odd primes,
`σ_{2j}(N) ≡ 2 + 2 N^{2j} (mod 64)`.
So the low 6 bits of the SIGK witness are an explicit polynomial in `N`: no separating
pair `N₁ ≡ N₂ (mod 2^k)` exists for any `k ≤ 6`.  The reason is 2-adic:
`8 ∣ p² - 1` for odd `p`, hence `64 ∣ (p^{2j} - 1)(q^{2j} - 1)`, and
`σ_k(N) = 2 + 2N^k - (p^k - 1)(q^k - 1)` identically.  A search over all semiprimes with
both prime factors below 300 finds no separating pair at `2^6`, matching the theorem.

**Positive result (7 bits do separate, and the separation is unconditional).**
`sigma_two_no_mod_formula`: at `2^7 = 128` the separation the paper asks for exists —
`15 = 3·5` and `527 = 17·31` satisfy `527 ≡ 15 (mod 128)` while
`σ₂(527) ≡ 68` and `σ₂(15) ≡ 4 (mod 128)`.  Hence **no function whatsoever** of
`N mod 128` — polynomial or not — computes `σ₂(N) mod 128` on odd semiprimes.  This is
strictly stronger than the polynomial barrier of `FreeWitnessClassification.lean`.
The same pair separates the modular circle count already at `2^5 = 32`
(`circleCount_no_mod_formula`), so CIRC is 2-adically *less* sealed than SIGK.

**Sharpness of the classification hypothesis.**
`sigma_zero_is_polynomial`: at `k = 0` the witness degenerates — `σ₀(pq) = 4` is
constant, hence a polynomial in `N` carrying no factor information at all.  So the
hypothesis `k ≥ 1` in `FreeWitness.classification_of_powerWeight` cannot be dropped.
-/

open FreeWitness

open ArithmeticFunction

/-! ## The 2-adic identity -/

theorem FreeWitness.eight_dvd_even_pow_sub_one{p : ℕ} (hp : Odd p) (j : ℕ) :
    (8 : ℤ) ∣ (p : ℤ) ^ (2 * j) - 1 := by sorry
