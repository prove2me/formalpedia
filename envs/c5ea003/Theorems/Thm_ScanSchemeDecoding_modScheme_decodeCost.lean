-- Prove2me | Theorems.Thm_ScanSchemeDecoding_modScheme_decodeCost
-- name    : ScanSchemeDecoding.modScheme_decodeCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:59.531538+00:00
-- url     : https://prove2.me/theorems/58364bdc-5c8e-4bb7-a467-4186adc87293
-- title:
--   The residue scheme attains the pigeonhole optimum exactly.
-- statement:
--   **The residue scheme attains the pigeonhole optimum exactly.**
--
--   ```lean
--   theorem ScanSchemeDecoding.modScheme_decodeCost(N : ℕ) {m : ℕ} (hm : 0 < m) :
--       ∑ x, (modScheme N hm).decodeCost x = triangleOpt N m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Optimum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Optimum.lean#L170

-- Thm stub generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

/-!
# The exact optimum of a scan scheme, and the pigeonhole failure analysis

Combining the exact cost accounting of `Algebra.ScanSchemeDecoding.Core` with the
exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` we obtain:

* `ScanSchemeDecoding.ScanScheme.triangleOpt_le_decodeCost` — **every** scan scheme on
  `N` keys with `m` bucket labels costs at least `triangleOpt N m`;
* `ScanSchemeDecoding.modScheme_decodeCost` — the residue scheme `x ↦ x % m` costs
  *exactly* `triangleOpt N m`;
* `ScanSchemeDecoding.scan_optimum` — hence `triangleOpt N m` is the least achievable
  total cost (`IsLeast`), an exact optimum rather than a bound;
* `ScanSchemeDecoding.ScanScheme.exists_costly_key` — the failure analysis: some key
  always costs at least the average bucket size, `N ≤ m * decodeCost x`;
* `ScanSchemeDecoding.ScanScheme.two_mul_decodeCost_ge` — the averaged `ε`-form.
-/

open ScanSchemeDecoding

open Finset

open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)






/-! ### The residue scheme attains the optimum -/

theorem ScanSchemeDecoding.modScheme_decodeCost(N : ℕ) {m : ℕ} (hm : 0 < m) :
    ∑ x, (modScheme N hm).decodeCost x = triangleOpt N m := by sorry
