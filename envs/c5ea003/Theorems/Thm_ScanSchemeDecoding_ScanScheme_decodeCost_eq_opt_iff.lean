-- Prove2me | Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq_opt_iff
-- name    : ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:57:15.040663+00:00
-- url     : https://prove2.me/theorems/d6fa1f81-0ef6-47a7-88b3-72f32f43d383
-- title:
--   Structure of the optimal schemes.
-- statement:
--   **Structure of the optimal schemes.**  A scan scheme decodes at optimal total cost
--   iff its bucket loads are balanced to within one key.
--
--   ```lean
--   theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff(hβ : 0 < Fintype.card β) :
--       ∑ x, S.decodeCost x = triangleOpt (Fintype.card α) (Fintype.card β) ↔
--         ∀ b : β, Fintype.card α / Fintype.card β ≤ (S.fiber b).card ∧
--           (S.fiber b).card ≤ Fintype.card α / Fintype.card β + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Rigidity.lean#L90

-- Thm stub generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

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

theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff(hβ : 0 < Fintype.card β) :
    ∑ x, S.decodeCost x = triangleOpt (Fintype.card α) (Fintype.card β) ↔
      ∀ b : β, Fintype.card α / Fintype.card β ≤ (S.fiber b).card ∧
        (S.fiber b).card ≤ Fintype.card α / Fintype.card β + 1 := by sorry
