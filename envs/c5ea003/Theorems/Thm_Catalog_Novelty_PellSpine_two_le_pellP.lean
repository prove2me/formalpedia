-- Prove2me | Theorems.Thm_Catalog_Novelty_PellSpine_two_le_pellP
-- name    : Catalog.Novelty.PellSpine.two_le_pellP
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:15:05.61898+00:00
-- url     : https://prove2.me/theorems/95d7f0f2-9582-4d51-a91b-941796e83e56
-- title:
--   `2 ≤ P n` once `n ≥ 2`; used to see that proper divisors of `P n` are nontrivial.
-- statement:
--   `2 ≤ P n` once `n ≥ 2`; used to see that proper divisors of `P n` are nontrivial.
--
--   ```lean
--   theorem Catalog.Novelty.PellSpine.two_le_pellP{n : ℕ} (hn : 2 ≤ n) : 2 ≤ pellP n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PellSpineCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PellSpineCore.lean#L186

-- Thm stub generated from Novelty/PellSpineCore.lean
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

theorem Catalog.Novelty.PellSpine.two_le_pellP{n : ℕ} (hn : 2 ≤ n) : 2 ≤ pellP n := by sorry
