-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.mean_decodeCost_ge_inv_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:18:35.951051+00:00
-- url     : https://prove2.me/submissions/af5b68b8-9906-4d67-bb01-d1cb37eba6ff

-- Sol generated from Algebra/ScanSchemeDecoding/Epsilon.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_triangleOpt_le_decodeCost
import Theorems.Thm_ScanSchemeDecoding_triangleOpt_mul_ge

/-!
# The `ε`-compression barrier for scan indices

The exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` is stated with the
*floor* `⌊N/m⌋`.  Here we sharpen it to a statement with genuine (real) division, which
is the form in which a space/time trade-off is usually quoted:

  `N * (N + m) ≤ 2 * m * triangleOpt N m`  (`triangleOpt_mul_ge`, an exact `ℕ` statement),

and deduce the analytic corollaries

* `mean_decodeCost_ge` — the mean decoding cost of any scan scheme is at least
  `(N/m + 1)/2`;
* `mean_decodeCost_ge_inv_two_mul` — the **`ε`-compression barrier**: a scheme whose
  index uses only `m ≤ ε · N` buckets has mean decoding cost at least `1/(2ε)`.

Both are sharp: for `m ∣ N` the residue scheme of `Algebra.ScanSchemeDecoding.Optimum`
meets the first bound with equality (`mean_decodeCost_modScheme_eq` for `m ∣ N`).
-/

open ScanSchemeDecoding

open Finset


open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)

/-- Division-free averaged bound for an arbitrary scan scheme. -/
theorem card_mul_ge (hβ : 0 < Fintype.card β) :
    Fintype.card α * (Fintype.card α + Fintype.card β)
      ≤ 2 * Fintype.card β * ∑ x, S.decodeCost x :=
  le_trans (triangleOpt_mul_ge hβ (Fintype.card α))
    (Nat.mul_le_mul_left _ (S.triangleOpt_le_decodeCost hβ))

/-- **Mean-cost lower bound.**  The average number of comparisons per decoded key is at
least `(N/m + 1)/2`, with *exact* real division. -/
theorem mean_decodeCost_ge (hα : 0 < Fintype.card α) (hβ : 0 < Fintype.card β) :
    ((Fintype.card α : ℝ) / (Fintype.card β : ℝ) + 1) / 2
      ≤ (∑ x, S.decodeCost x : ℝ) / (Fintype.card α : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hα
  have hmpos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hβ
  have hkey : (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) + (Fintype.card β : ℝ))
      ≤ 2 * (Fintype.card β : ℝ) * ((∑ x, S.decodeCost x : ℕ) : ℝ) := by
    exact_mod_cast card_mul_ge S hβ
  rw [div_le_div_iff₀ (by norm_num) hNpos, div_add' _ _ _ (ne_of_gt hmpos)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hmpos]
  push_cast at hkey ⊢
  nlinarith [hkey, hNpos, hmpos]





namespace ScanSchemeDecoding.ScanScheme
/-- Division-free averaged bound for an arbitrary scan scheme. -/
theorem card_mul_ge (hβ : 0 < Fintype.card β) :
    Fintype.card α * (Fintype.card α + Fintype.card β)
      ≤ 2 * Fintype.card β * ∑ x, S.decodeCost x :=
  le_trans (triangleOpt_mul_ge hβ (Fintype.card α))
    (Nat.mul_le_mul_left _ (S.triangleOpt_le_decodeCost hβ))

end ScanSchemeDecoding.ScanScheme

namespace ScanSchemeDecoding.ScanScheme


end ScanSchemeDecoding.ScanScheme

open ScanSchemeDecoding in
theorem solution(eps : ℝ) (heps : 0 < eps)
    (hα : 0 < Fintype.card α) (hβ : 0 < Fintype.card β)
    (hcomp : (Fintype.card β : ℝ) ≤ eps * (Fintype.card α : ℝ)) :
    1 / (2 * eps) ≤ (∑ x, S.decodeCost x : ℝ) / (Fintype.card α : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hα
  have hmpos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hβ
  refine le_trans ?_ (mean_decodeCost_ge S hα hβ)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have hdiv : 1 / eps ≤ (Fintype.card α : ℝ) / (Fintype.card β : ℝ) := by
    rw [div_le_div_iff₀ heps hmpos, one_mul]
    linarith
  have hone : (0 : ℝ) ≤ 1 := by norm_num
  have hstep : 1 / eps ≤ (Fintype.card α : ℝ) / (Fintype.card β : ℝ) + 1 := by linarith
  calc (1 : ℝ) * 2 = 2 * eps * (1 / eps) := by field_simp
    _ ≤ 2 * eps * ((Fintype.card α : ℝ) / (Fintype.card β : ℝ) + 1) := by
        have h2e : (0 : ℝ) < 2 * eps := by linarith
        exact mul_le_mul_of_nonneg_left hstep (le_of_lt h2e)
    _ = ((Fintype.card α : ℝ) / (Fintype.card β : ℝ) + 1) * (2 * eps) := by ring
