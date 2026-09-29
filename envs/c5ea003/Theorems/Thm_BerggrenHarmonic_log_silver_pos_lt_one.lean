-- Prove2me | Theorems.Thm_BerggrenHarmonic_log_silver_pos_lt_one
-- name    : BerggrenHarmonic.log_silver_pos_lt_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:15:05.59425+00:00
-- url     : https://prove2.me/theorems/35646916-af8b-44ac-b7b7-ae848bd37910
-- title:
--   The numerical input to the refutation: `0 < log(1+√2) < 1`.
-- statement:
--   The numerical input to the refutation: `0 < log(1+√2) < 1`.
--
--   ```lean
--   theorem BerggrenHarmonic.log_silver_pos_lt_one:
--       0 < Real.log (1 + Real.sqrt 2) ∧ Real.log (1 + Real.sqrt 2) < 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenTransferSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenTransferSpectrum.lean#L161

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




/-! ## Refuting the silver-ratio spectral gap -/

theorem BerggrenHarmonic.log_silver_pos_lt_one:
    0 < Real.log (1 + Real.sqrt 2) ∧ Real.log (1 + Real.sqrt 2) < 1 := by sorry
