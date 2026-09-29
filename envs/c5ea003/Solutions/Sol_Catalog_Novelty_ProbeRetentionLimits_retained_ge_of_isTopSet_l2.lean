-- Prove2me | solution 1 for Catalog.Novelty.ProbeRetentionLimits.retained_ge_of_isTopSet_l2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:17:04.197382+00:00
-- url     : https://prove2.me/submissions/779fada8-e033-4f7f-a886-188fa8bc1e12

-- Sol generated from Novelty/ProbeRetentionLimits.lean
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_ProbeRetentionLimits
import Theorems.Thm_Catalog_Novelty_ProbeRetentionLimits_sum_sdiff_le_of_isTopSet

/-!
# How much retention can a content probe buy? (NET-69, selection layer)

NET-69 runs the NET-58/61 eviction methodology on Python source instead of
prose.  Three arms select `B = 64` keys out of a context and are scored by the
**retained attention mass** of the selected set:

| arm                | retained @ B = 64 |
|--------------------|-------------------|
| accumulated-HH     | 0.9340            |
| probe-only         | 0.8149            |
| hybrid (λ = 1)     | 0.9371            |

and the linear content probe explains `R² = 0.3185` of the variance of the true
importances (prose: `0.329`).  The verdict advertised for the round is
*CONTENT-WEAKNESS-IS-DOMAIN-UNIVERSAL*.

This file is the **selection-theoretic layer** of that verdict.  A key insight
of the round — that a *low* `R²` is what makes the probe arm lose — is a claim
about the map

  `prediction accuracy  ↦  retained mass`,

and that map is exactly what can be analysed rigorously.  We fix a finite index
type of keys, true importances `a : ι → ℝ`, a score `s : ι → ℝ`, and define a
**top set** `IsTopSet s B S`: a set of `B` keys none of which is scored below a
discarded key.  This is the (possibly non-unique) output of a greedy budget-`B`
evictor driven by `s`.

The results:

* `sum_le_sum_of_isTopSet` — a top set maximises the *score* mass among all
  budget-`B` sets.  Everything else is a perturbation of this.
* `retained_le_of_isTopSet_true` — with `s = a` one recovers the oracle bound:
  no budget-`B` policy beats the top-`B` true set (`P2`, second clause, in its
  provable form).
* `retained_ge_of_isTopSet_sup` and `retained_ge_of_isTopSet_l2` — the two
  **transfer theorems**: a score whose error is small in `L∞` (resp. `L²`)
  retains almost as much as *any* competing budget-`B` set, with explicit
  losses `2Bε` and `2√(B · SSE)`.
* `retention_gap_le_of_Rsq` — the transfer theorem stated in the currency of the
  experiment: the loss of an `R²`-accurate probe against any rival arm is at
  most `2√(B (1 - R²) · SS_tot)`.
* `net69_dispersion_lower_bound` — read backwards, the *measured* 11.91-point
  loss of the probe arm at `B = 64, R² = 0.3185` is a **lower bound on the
  dispersion of the true importances**: `SS_tot > 8 · 10⁻⁵`.  A measurement of
  the probe deficit is therefore also a measurement of the key population; the
  two numbers are not independent.
* `bound_ratio_code_prose_lt_one_percent` — the code and prose `R²` values
  (`0.3185` vs `0.329`) give worst-case losses within `0.8 %` of each other.
  This is the *quantitative content* of "domain-universal": the two rounds are
  not merely qualitatively similar, they are numerically indistinguishable at
  the level of the guarantee.
* `exists_probe_perfect_retention_with_Rsq` — the **critical** result.  For
  *every* target `R² = ρ ∈ (0,1)` there is a probe with exactly that `R²` that
  reproduces the oracle set for *every* budget.  Hence `R² = 0.32` by itself
  cannot explain the 12-point loss: the loss is caused by the *direction* of
  the residual, never by its size alone.  The bound above is one-sided, and
  provably so.
-/

open Catalog.Novelty.ProbeRetentionLimits

open Finset

variable {ι : Type*} [Fintype ι]

/-! ### 1. Budget-`B` selection and top sets -/





omit [Fintype ι] in
/-- **A top set maximises score mass.**  Every competing set of the same size
carries at most as much `s`-mass. -/
lemma sum_le_sum_of_isTopSet {s : ι → ℝ} {B : ℕ} {S T : Finset ι}
    (hS : IsTopSet s B S) (hT : T.card = B) : ∑ i ∈ T, s i ≤ ∑ i ∈ S, s i := by
  classical
  have key := sum_sdiff_le_of_isTopSet hS hT
  have hTsplit : ∑ i ∈ T ∩ S, s i + ∑ i ∈ T \ S, s i = ∑ i ∈ T, s i :=
    Finset.sum_inter_add_sum_diff T S s
  have hSsplit : ∑ i ∈ S ∩ T, s i + ∑ i ∈ S \ T, s i = ∑ i ∈ S, s i :=
    Finset.sum_inter_add_sum_diff S T s
  have hcomm : T ∩ S = S ∩ T := Finset.inter_comm T S
  rw [← hTsplit, ← hSsplit, hcomm]
  gcongr



/-! ### 2. The two transfer theorems -/



/-- Cauchy–Schwarz on a selected block: the accumulated prediction error of any
`k`-element set is at most `√(k · SSE)`. -/
lemma abs_sum_error_le (a s : ι → ℝ) (S : Finset ι) :
    |∑ i ∈ S, (a i - s i)| ≤ Real.sqrt (S.card * sse a s) := by
  have h1 : (∑ i ∈ S, (a i - s i)) ^ 2 ≤ S.card * ∑ i ∈ S, (a i - s i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ i ∈ S, (a i - s i) ^ 2 ≤ sse a s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => sq_nonneg _)
  have h3 : (∑ i ∈ S, (a i - s i)) ^ 2 ≤ S.card * sse a s :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  exact Real.abs_le_sqrt h3





/-! ### 3. `R²` and the measured NET-69 numbers -/









/-! ### 4. `R²` cannot be the mechanism -/






/-! ### 5. The boundary band: where the loss actually lives -/




open Catalog.Novelty.ProbeRetentionLimits in
theorem solution{a s : ι → ℝ} {B : ℕ} {S T : Finset ι}
    (hS : IsTopSet s B S) (hT : T.card = B) :
    retained a T - 2 * Real.sqrt (B * sse a s) ≤ retained a S := by
  have hscore : ∑ i ∈ T, s i ≤ ∑ i ∈ S, s i := sum_le_sum_of_isTopSet hS hT
  have hSe : |∑ i ∈ S, (a i - s i)| ≤ Real.sqrt (B * sse a s) := by
    have := abs_sum_error_le a s S
    rwa [hS.1] at this
  have hTe : |∑ i ∈ T, (a i - s i)| ≤ Real.sqrt (B * sse a s) := by
    have := abs_sum_error_le a s T
    rwa [hT] at this
  have hSsplit : retained a S = ∑ i ∈ S, s i + ∑ i ∈ S, (a i - s i) := by
    simp [retained, Finset.sum_sub_distrib]
  have hTsplit : retained a T = ∑ i ∈ T, s i + ∑ i ∈ T, (a i - s i) := by
    simp [retained, Finset.sum_sub_distrib]
  have h1 := (abs_le.mp hSe).1
  have h2 := (abs_le.mp hTe).2
  rw [hSsplit, hTsplit]
  linarith
