-- Prove2me | Theorems.Thm_DDAG_descProduct_eq_gammaSeq
-- name    : DDAG.descProduct_eq_gammaSeq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:36:45.655462+00:00
-- url     : https://prove2.me/theorems/3ce08914-e81f-40c8-bc37-6fd22ebda54f
-- title:
--   Relation between the mean-growth product and Mathlib's `Real.GammaSeq`:
-- statement:
--   Relation between the mean-growth product and Mathlib's `Real.GammaSeq`:
--   `P_n(a) = n^a / (a · GammaSeq a n)` for `n ≥ 1`.
--
--   ```lean
--   theorem DDAG.descProduct_eq_gammaSeq{a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
--       descProduct a n = (n : ℝ) ^ a / (a * Real.GammaSeq a n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DescendantScaling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DescendantScaling.lean#L59

-- Thm stub generated from Applications/DescendantScaling.lean
import Mathlib
import Definitions.Def_Applications_DescendantScaling

/-!
# The `n^{1/d}` scaling of descendant counts in random `d`-DAGs

For the random recursive DAG `G_n` with out-degree `d ≥ 2`, the number of descendants
`|D_n|` grows like `n^{1/d}`; this is precisely the normalisation appearing in the limit
law `|D_n| / n^{1/d} ⟶ Gamma(d, 1)` (Janson, 2023).

The mean growth is governed by a product of the form
`P_n(a) = ∏_{k=1}^n (1 + a/k)` with `a = 1/d`: each new vertex attaches to earlier
vertices, contributing a multiplicative factor `1 + a/k`.  This file proves, fully
formally, two facts about this product.

* `descProduct_gamma_closed_form` : the exact closed form
  `P_n(a) = Γ(n+1+a) / (Γ(1+a) · n!)`;
* `descProduct_div_rpow_tendsto` : the scaling limit
  `P_n(a) / n^a ⟶ 1 / Γ(1+a)` as `n → ∞`,

and specialises the latter to the `d`-DAG normalisation:

* `ddag_descProduct_scaling` : `P_n(1/d) / n^{1/d} ⟶ 1 / Γ(1 + 1/d)`.

In particular the correct scaling exponent is `1/d`, matching the statement of the limit
theorem, and the multiplicative constant is `1/Γ(1 + 1/d)`.
-/

open Real Filter Topology

open DDAG

theorem DDAG.descProduct_eq_gammaSeq{a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    descProduct a n = (n : ℝ) ^ a / (a * Real.GammaSeq a n) := by sorry
