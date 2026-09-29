-- Prove2me | Definitions.Def_Bridges_BerggrenTransferSpectrum
-- name    : Bridges_BerggrenTransferSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:15.61824+00:00
-- url     : https://prove2.me/theorems/0916c3b4-44f4-4c7e-901c-08f687c4e645
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTransferSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTransferSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTransferSpectrum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_BerggrenHarmonicMeasure

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

namespace BerggrenHarmonic

open Finset

/-- The transfer (Markov) operator of the Berggren walk on boundary functions. -/
noncomputable def transfer (P : ProbVec) (f : Bdry → ℝ) : Bdry → ℝ :=
  fun x => ∑ a, P.p a * f (cons a x)

/-- `f` is determined by the first `n` letters of its argument. -/
def DependsOn (n : ℕ) (f : Bdry → ℝ) : Prop :=
  ∀ x y : Bdry, (∀ i < n, x i = y i) → f x = f y







/-! ## The spectrum on locally constant functions -/




/-! ## Refuting the silver-ratio spectral gap -/



end BerggrenHarmonic


