-- Prove2me | Theorems.Thm_BerggrenHarmonic_eigenvalue_eq_zero_or_one
-- name    : BerggrenHarmonic.eigenvalue_eq_zero_or_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:16:38.73022+00:00
-- url     : https://prove2.me/theorems/f1f2ec77-b37c-4668-90f7-514d9561be5b
-- title:
--   **The spectrum of the Berggren transfer operator on locally constant functions is
-- statement:
--   **The spectrum of the Berggren transfer operator on locally constant functions is
--   `{0, 1}`.**  A nonzero locally constant eigenfunction forces the eigenvalue to be `0` or
--   `1`; equivalently the Markov operator has spectral gap `1`, for *every* choice of the
--   weights `(p₁, p₂, p₃)`.
--
--   ```lean
--   theorem BerggrenHarmonic.eigenvalue_eq_zero_or_one(P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
--       {c : ℝ} (hc : transfer P f = fun x => c * f x) (hne : ∃ x, f x ≠ 0) :
--       c = 0 ∨ c = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenTransferSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenTransferSpectrum.lean#L124

-- Thm stub generated from Bridges/BerggrenTransferSpectrum.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenHarmonicMeasure
import Definitions.Def_Bridges_BerggrenTransferSpectrum

/-!
# The transfer operator of the Berggren walk and its spectrum

The Markov operator of the Berggren random walk acts on functions on the boundary
`Bdry = ℕ → Fin 3` by

`(L f)(x) = p₁ f(1·x) + p₂ f(2·x) + p₃ f(3·x)`,

where `a·x = cons a x` prepends the Berggren move `a`.  This is the operator whose fixed
points are the harmonic functions of the walk and whose invariant measure is the harmonic
measure `bernoulli P` of `Catalog.Bridges.BerggrenHarmonicMeasure`.

The conjecture motivating this cycle was that the *spectral gap* of the Berggren walk is
governed by the silver ratio `1 + √2` of the tree's metric growth.  The results below show
that this is false in a strong and clean way: on the natural core of locally constant
functions (the union of the finite-dimensional spaces `DependsOn n`, which is dense in every
reasonable completion), the transfer operator is **nilpotent modulo constants**.

## Main results

* `transfer_dependsOn` : `L` maps functions of the first `n+1` letters to functions of the
  first `n` letters — the operator strictly decreases the "memory" of a function.
* `iterate_transfer_const` : hence `Lⁿ f` is *constant* for every `f` depending on the first
  `n` letters.  This is the nilpotency statement.
* `eigenvalue_eq_zero_or_one` : consequently every eigenvalue of `L` on locally constant
  functions is `0` or `1`, and (`eigenfunction_one_isConst`) the eigenvalue `1` has only the
  constants as eigenfunctions.  The **spectral gap is `1`, independently of `(p₁,p₂,p₃)`**.
* `log_silver_not_eigenvalue` : in particular `log(1+√2)` — the growth exponent of the
  Berggren tree — is *not* an eigenvalue of the Markov operator: the conjectured
  silver-ratio spectral gap is refuted.  (`log_silver_pos_lt_one` isolates the numerical
  fact `0 < log(1+√2) < 1` on which the refutation rests.)
-/

open BerggrenHarmonic

open Finset









/-! ## The spectrum on locally constant functions -/

theorem BerggrenHarmonic.eigenvalue_eq_zero_or_one(P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
    {c : ℝ} (hc : transfer P f = fun x => c * f x) (hne : ∃ x, f x ≠ 0) :
    c = 0 ∨ c = 1 := by sorry
