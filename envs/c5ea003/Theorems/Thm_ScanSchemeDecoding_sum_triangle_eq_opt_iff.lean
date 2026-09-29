-- Prove2me | Theorems.Thm_ScanSchemeDecoding_sum_triangle_eq_opt_iff
-- name    : ScanSchemeDecoding.sum_triangle_eq_opt_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:57:42.805731+00:00
-- url     : https://prove2.me/theorems/ceddc96e-f05e-4c3b-a8d5-d486e3483620
-- title:
--   Rigidity of the pigeonhole optimum.
-- statement:
--   **Rigidity of the pigeonhole optimum.**  A size profile realises the optimum iff
--   every bucket size deviates from the mean `⌊N/m⌋` by at most one *upwards* and not at
--   all downwards.
--
--   ```lean
--   theorem ScanSchemeDecoding.sum_triangle_eq_opt_iff{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ)
--       (hf : ∑ i, f i = N) :
--       ∑ i, triangle (f i) = triangleOpt N m ↔ ∀ i, N / m ≤ f i ∧ f i ≤ N / m + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Rigidity.lean#L29

-- Thm stub generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
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

theorem ScanSchemeDecoding.sum_triangle_eq_opt_iff{m : ℕ} (hm : 0 < m) (f : Fin m → ℕ) (N : ℕ)
    (hf : ∑ i, f i = N) :
    ∑ i, triangle (f i) = triangleOpt N m ↔ ∀ i, N / m ≤ f i ∧ f i ≤ N / m + 1 := by sorry
