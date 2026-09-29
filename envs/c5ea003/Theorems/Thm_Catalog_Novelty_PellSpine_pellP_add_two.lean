-- Prove2me | Theorems.Thm_Catalog_Novelty_PellSpine_pellP_add_two
-- name    : Catalog.Novelty.PellSpine.pellP_add_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:13:55.809981+00:00
-- url     : https://prove2.me/theorems/76208e1f-db6b-4b9f-bf6e-db078decf5d0
-- title:
--   PellP add two
-- statement:
--   Formal statement of `Catalog.Novelty.PellSpine.pellP_add_two` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.PellSpine.pellP_add_two(n : ℕ) : pellP (n + 2) = 2 * pellP (n + 1) + pellP n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PellSpineCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PellSpineCore.lean#L51

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

theorem Catalog.Novelty.PellSpine.pellP_add_two(n : ℕ) : pellP (n + 2) = 2 * pellP (n + 1) + pellP n := by sorry
