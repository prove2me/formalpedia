-- Prove2me | solution 1 for DDAG.descProduct_eq_gammaSeq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:23:57.925649+00:00
-- url     : https://prove2.me/submissions/4d26fbf3-0df3-4d8c-940f-845eacd2106a

-- Sol generated from Applications/DescendantScaling.lean
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









open DDAG in
theorem solution{a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    descProduct a n = (n : ℝ) ^ a / (a * Real.GammaSeq a n) := by
  have h_gamma_seq : Real.GammaSeq a n = (n : ℝ) ^ a * Nat.factorial n / (∏ j ∈ Finset.range (n + 1), (a + j)) := by
    rw [ Real.GammaSeq, Finset.prod_range_succ' ];
  -- By definition of `descProduct`, we have:
  have h_descProduct : descProduct a n = (∏ k ∈ Finset.Icc 1 n, (a + k)) / (Nat.factorial n) := by
    unfold descProduct;
    rw [ Finset.prod_congr rfl fun x hx => by rw [ one_add_div ( by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) ] ];
    norm_num [ add_comm, Finset.prod_div_distrib ];
    erw [ ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial ];
  have h_prod_range : ∏ j ∈ Finset.range (n + 1), (a + j) = a * ∏ k ∈ Finset.Icc 1 n, (a + k) := by
    erw [ Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, mul_comm, Finset.prod_range_succ' ];
  simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  simp +decide [ ha.ne', ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) _ ) ]
