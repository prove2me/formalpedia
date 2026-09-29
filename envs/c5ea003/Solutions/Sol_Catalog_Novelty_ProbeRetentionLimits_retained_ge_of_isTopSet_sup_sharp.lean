-- Prove2me | solution 1 for Catalog.Novelty.ProbeRetentionLimits.retained_ge_of_isTopSet_sup_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:18:48.554632+00:00
-- url     : https://prove2.me/submissions/f257c14a-8bb7-4d06-9698-8e94c57b5f4f

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








/-! ### 2. The two transfer theorems -/








/-! ### 3. `R²` and the measured NET-69 numbers -/









/-! ### 4. `R²` cannot be the mechanism -/






/-! ### 5. The boundary band: where the loss actually lives -/




open Catalog.Novelty.ProbeRetentionLimits in
omit [Fintype ι] in
theorem solution[DecidableEq ι] {a s : ι → ℝ} {B : ℕ} {S T : Finset ι} {ε : ℝ}
    (hS : IsTopSet s B S) (hT : T.card = B) (hε : ∀ i, |a i - s i| ≤ ε) :
    retained a T - 2 * (S \ T).card * ε ≤ retained a S := by
  classical
  have key := sum_sdiff_le_of_isTopSet hS hT
  have hdiff : (S \ T).card = (T \ S).card :=
    Finset.card_sdiff_comm (by rw [hS.1, hT])
  have hbound : ∀ U : Finset ι, |∑ i ∈ U, (a i - s i)| ≤ U.card * ε := by
    intro U
    calc |∑ i ∈ U, (a i - s i)| ≤ ∑ i ∈ U, |a i - s i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ U, ε := Finset.sum_le_sum (fun i _ => hε i)
      _ = U.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  have hSd : |∑ i ∈ S \ T, (a i - s i)| ≤ (S \ T).card * ε := hbound _
  have hTd : |∑ i ∈ T \ S, (a i - s i)| ≤ (T \ S).card * ε := hbound _
  rw [← hdiff] at hTd
  have hSsum : ∑ i ∈ S \ T, a i = ∑ i ∈ S \ T, s i + ∑ i ∈ S \ T, (a i - s i) := by
    simp [Finset.sum_sub_distrib]
  have hTsum : ∑ i ∈ T \ S, a i = ∑ i ∈ T \ S, s i + ∑ i ∈ T \ S, (a i - s i) := by
    simp [Finset.sum_sub_distrib]
  have hsplitS : ∑ i ∈ S ∩ T, a i + ∑ i ∈ S \ T, a i = retained a S :=
    Finset.sum_inter_add_sum_diff S T a
  have hsplitT : ∑ i ∈ T ∩ S, a i + ∑ i ∈ T \ S, a i = retained a T :=
    Finset.sum_inter_add_sum_diff T S a
  have hcomm : T ∩ S = S ∩ T := Finset.inter_comm T S
  rw [hcomm] at hsplitT
  have h1 := (abs_le.mp hSd).1
  have h2 := (abs_le.mp hTd).2
  rw [← hsplitS, ← hsplitT, hSsum, hTsum]
  linarith
