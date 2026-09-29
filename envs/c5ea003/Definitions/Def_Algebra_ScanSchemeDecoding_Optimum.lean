-- Prove2me | Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
-- name    : Algebra_ScanSchemeDecoding_Optimum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:13:22.848158+00:00
-- url     : https://prove2.me/theorems/4cf40142-8864-4644-9d33-b8444f460184
-- title:
--   Aether Catalog definitions — Algebra_ScanSchemeDecoding_Optimum
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ScanSchemeDecoding.Optimum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ScanSchemeDecoding/Optimum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core

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

namespace ScanSchemeDecoding

open Finset

namespace ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)





end ScanScheme

/-! ### The residue scheme attains the optimum -/


/-- The **residue scan scheme**: store key `x` in bucket `x % m`. -/
def modScheme (N : ℕ) {m : ℕ} (hm : 0 < m) : ScanScheme (Fin N) (Fin m) :=
  ⟨fun x => ⟨(x : ℕ) % m, Nat.mod_lt _ hm⟩⟩




end ScanSchemeDecoding


