-- Prove2me | Theorems.Thm_MordellDenominators_exists_reduction
-- name    : MordellDenominators.exists_reduction
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:11.172713+00:00
-- url     : https://prove2.me/theorems/79ca247d-eeef-456f-b3fc-6b2e825d5742
-- title:
--   Good reduction of the point.
-- statement:
--   **Good reduction of the point.**  If `ℓ` does not divide the denominator of
--   `x`, the point reduces to an affine point of `E_N` over `𝔽_ℓ = ZMod ℓ`.
--
--   ```lean
--   theorem MordellDenominators.exists_reduction{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
--       (hl : l.Prime) (hnd : ¬ l ∣ x.den) :
--       ∃ X Y : ZMod l, Y ^ 2 = X ^ 3 + (N : ZMod l) ∧
--         X * (x.den : ZMod l) = (x.num : ZMod l) ∧
--         Y * (y.den : ZMod l) = (y.num : ZMod l) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Reduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Reduction.lean#L25

-- Thm stub generated from Cryptography/MordellDenominators/Reduction.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic

/-!
# Reduction modulo `ℓ` and the meaning of a denominator prime

This file explains *why* good primes can occur in denominators.  Writing a
rational point of `E_N : y² = x³ + N` as `x = a/e²`, `y = b/e³` we obtain the
integral model `b² = a³ + N e⁶` (`curve_integral_model`, proved in
`Basic.lean`), and then a clean dichotomy for every prime
`ℓ`:

* if `ℓ ∤ x.den`, the point **reduces to an affine point** of `E_N(𝔽_ℓ)`
  (`MordellDenominators.exists_reduction`);
* if `ℓ ∣ x.den`, the point has **no affine reduction** — it reduces to the
  point at infinity `O` (`MordellDenominators.no_affine_reduction`).

Consequently a prime — good or bad — occurs in a denominator exactly when the
point falls into the kernel of reduction at that prime
(`MordellDenominators.dvd_den_iff_no_affine_reduction`).  Nothing in this
mechanism refers to the discriminant, which is the structural reason why the
"only bad primes" conjecture had to fail.
-/

open MordellDenominators

theorem MordellDenominators.exists_reduction{N : ℤ} {x y : ℚ} (h : OnCurve N x y) {l : ℕ}
    (hl : l.Prime) (hnd : ¬ l ∣ x.den) :
    ∃ X Y : ZMod l, Y ^ 2 = X ^ 3 + (N : ZMod l) ∧
      X * (x.den : ZMod l) = (x.num : ZMod l) ∧
      Y * (y.den : ZMod l) = (y.num : ZMod l) := by sorry
