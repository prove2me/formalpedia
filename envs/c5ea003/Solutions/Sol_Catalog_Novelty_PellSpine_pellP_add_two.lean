-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellP_add_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:47:37.636729+00:00
-- url     : https://prove2.me/submissions/2aa8449b-a3f6-460a-86a4-9b8b018463e7

-- Sol generated from Novelty/PellSpineCore.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
/-
# The Pell spine: core arithmetic of the silver-ratio recursion

The *silver ratio* `1 + √2` is the fundamental unit of `ℤ[√2]`, and it already appears
throughout the catalog (`Novelty.BerggrenTreeCriticalLine.silverUnit`,
`Novelty.HyperbolicBerggrenSilverGrowth.silver`, `Shared.BerggrenTQC.SilverSpectrum`).
Its integral shadow is the pair of sequences

* `pellP` : `0, 1, 2, 5, 12, 29, 70, 169, 408, …`  (Pell numbers, OEIS A000129)
* `pellQ` : `1, 1, 3, 7, 17, 41, 99, 239, 577, …`  (half-companion Pell, OEIS A001333)

determined by `(1 + √2)ⁿ = pellQ n + pellP n · √2`.

This file develops the *core* arithmetic of the pair — everything the downstream files
(`Novelty.PellSpineDivisibility`, `Novelty.PellSpinePythagorean`) need:

* `pellP_add`, `pellQ_add` — the two addition laws, proved by a single simultaneous
  two-step induction;
* `pell_equation` — `Q n ^ 2 - 2 * P n ^ 2 = (-1)^n` over `ℤ`, the unit-norm identity;
* `pellP_coprime_pellQ` — its immediate corollary, the key coprimality input for the
  strong-divisibility theory;
* `pellMat_pow` — the *algebraic bridge*: `!![2,1;1,0] ^ (n+1) = !![P (n+2), P (n+1); P (n+1), P n]`,
  from which `pell_cassini` drops out of multiplicativity of the determinant;
* growth and monotonicity facts.

No result here is definitional: each identity needs either an induction or the
determinant bridge.
-/

open Catalog.Novelty.PellSpine

/-! ## Definitions -/





/-! ## The mutual one-step laws -/







/-! ## Addition laws

The two laws must be proved *together*: each inductive step feeds the other. -/







/-! ## The Pell equation and coprimality -/



/-! ## Growth -/







/-! ## The algebraic bridge: powers of the silver matrix -/





open Catalog.Novelty.PellSpine in
theorem solution(n : ℕ) : pellP (n + 2) = 2 * pellP (n + 1) + pellP n := rfl
