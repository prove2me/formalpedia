-- Prove2me | solution 1 for BerggrenHarmonic.log_silver_pos_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:12.120438+00:00
-- url     : https://prove2.me/submissions/069c9dc3-4acf-46f8-b5f8-c852f9e29ad3

-- Sol generated from Bridges/BerggrenTransferSpectrum.lean
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




open BerggrenHarmonic in
theorem solution:
    0 < Real.log (1 + Real.sqrt 2) ∧ Real.log (1 + Real.sqrt 2) < 1 := by
  have h2 : Real.sqrt 2 < 1.5 := by
    have : Real.sqrt 2 < Real.sqrt 2.25 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h225 : Real.sqrt 2.25 = 1.5 := by
      rw [show (2.25 : ℝ) = 1.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h225 ▸ this]
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · exact Real.log_pos (by linarith)
  · have he : (1 : ℝ) + Real.sqrt 2 < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    calc Real.log (1 + Real.sqrt 2) < Real.log (Real.exp 1) :=
          Real.log_lt_log (by linarith) he
      _ = 1 := Real.log_exp 1
