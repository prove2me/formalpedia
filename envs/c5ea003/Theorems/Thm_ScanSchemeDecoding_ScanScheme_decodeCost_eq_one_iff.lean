-- Prove2me | Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq_one_iff
-- name    : ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:57:22.032217+00:00
-- url     : https://prove2.me/theorems/2dcab597-4c0e-441e-ba2a-fc54966959be
-- title:
--   Perfect hashing.
-- statement:
--   **Perfect hashing.**  Every key decodes in one step iff the bucket map is injective.
--
--   ```lean
--   theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff: (∀ x, S.decodeCost x = 1) ↔ Function.Injective S.bucket := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Rigidity.lean#L117

-- Thm stub generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum

/-!
# Rigidity of the optimum, collision-freeness, and symmetry of the cost

The lower bound of `Algebra.ScanSchemeDecoding.Optimum` is not only sharp, it is
*rigid*: the tangent-line argument leaves a slack `(d)(d-1)/2` in each bucket, where
`d` is the deviation of the bucket size from `⌊N/m⌋`.  Since `d(d-1) = 0` only for
`d ∈ {0, 1}`, the optimum is attained **exactly** by the balanced size profiles.

## Main results

* `ScanSchemeDecoding.sum_triangle_eq_opt_iff` — rigidity at the level of size profiles.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff` — a scan scheme is cost-optimal
  iff every bucket has size `⌊N/m⌋` or `⌈N/m⌉`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff` — unit decoding cost everywhere
  is *equivalent* to injectivity of the bucket map (perfect hashing).
* `ScanSchemeDecoding.ScanScheme.exists_two_le_decodeCost` — fewer buckets than keys
  forces a key of cost `≥ 2`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_perm_invariant`,
  `ScanSchemeDecoding.ScanScheme.decodeCost_relabel` — the total cost is invariant under
  the natural `Sym(α) × Sym(β)`-action, i.e. it is a function of the bucket-size
  partition alone.
-/

open ScanSchemeDecoding

open Finset


open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)


omit [Fintype β] in

theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff: (∀ x, S.decodeCost x = 1) ↔ Function.Injective S.bucket := by sorry
