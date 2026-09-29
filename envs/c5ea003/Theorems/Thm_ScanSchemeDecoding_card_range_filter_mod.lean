-- Prove2me | Theorems.Thm_ScanSchemeDecoding_card_range_filter_mod
-- name    : ScanSchemeDecoding.card_range_filter_mod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:47.98127+00:00
-- url     : https://prove2.me/theorems/8f9a05c1-ff8a-4775-8bb8-1670683cc311
-- title:
--   Counting the residues below `N`: exactly `⌈(N - j)/m⌉` naturals below `N` are
-- statement:
--   Counting the residues below `N`: exactly `⌈(N - j)/m⌉` naturals below `N` are
--   congruent to `j` mod `m`, i.e. `N / m` plus one more when `j < N % m`.
--
--   ```lean
--   theorem ScanSchemeDecoding.card_range_filter_mod{m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j < m) (N : ℕ) :
--       ((Finset.range N).filter (fun x => x % m = j)).card
--         = N / m + (if j < N % m then 1 else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Optimum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Optimum.lean#L103

-- Thm stub generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum

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

theorem ScanSchemeDecoding.card_range_filter_mod{m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j < m) (N : ℕ) :
    ((Finset.range N).filter (fun x => x % m = j)).card
      = N / m + (if j < N % m then 1 else 0) := by sorry
