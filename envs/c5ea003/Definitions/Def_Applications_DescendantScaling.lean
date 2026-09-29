-- Prove2me | Definitions.Def_Applications_DescendantScaling
-- name    : Applications_DescendantScaling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:41:41.693564+00:00
-- url     : https://prove2.me/theorems/b1b907b2-0de4-4c78-acf6-cb4dfdbbf357
-- title:
--   Aether Catalog definitions — Applications_DescendantScaling
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DescendantScaling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DescendantScaling.lean by skeleton subtraction
import Mathlib

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

namespace DDAG

/-- The mean-growth product `P_n(a) = ∏_{k=1}^n (1 + a/k)`. With `a = 1/d` its order of
growth is the descendant normalisation `n^{1/d}`. -/
noncomputable def descProduct (a : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 n, (1 + a / (k : ℝ))







end DDAG


