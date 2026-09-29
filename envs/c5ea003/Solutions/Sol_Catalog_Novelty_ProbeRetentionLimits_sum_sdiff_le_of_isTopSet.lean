-- Prove2me | solution 1 for Catalog.Novelty.ProbeRetentionLimits.sum_sdiff_le_of_isTopSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:14:13.616194+00:00
-- url     : https://prove2.me/submissions/fb7b72c5-9f63-4030-a386-ad7fa5bbc548

-- Sol generated from Novelty/ProbeRetentionLimits.lean
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_ProbeRetentionLimits

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
theorem solution[DecidableEq ι] {s : ι → ℝ} {B : ℕ} {S T : Finset ι}
    (hS : IsTopSet s B S) (hT : T.card = B) :
    ∑ i ∈ T \ S, s i ≤ ∑ i ∈ S \ T, s i := by
  classical
  have hcard : S.card = T.card := by rw [hS.1, hT]
  have hdiff : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hcard
  rcases (T \ S).eq_empty_or_nonempty with he | hne
  · have : (S \ T).card = 0 := by rw [hdiff, he]; simp
    have hS' : S \ T = ∅ := Finset.card_eq_zero.mp this
    simp [he, hS']
  · have hne' : (S \ T).Nonempty := by
      rw [← Finset.card_pos, hdiff, Finset.card_pos]; exact hne
    obtain ⟨i₀, hi₀, hi₀min⟩ := Finset.exists_min_image (S \ T) s hne'
    obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image (T \ S) s hne
    have hi₀S : i₀ ∈ S := (Finset.mem_sdiff.mp hi₀).1
    have hj₀S : j₀ ∉ S := (Finset.mem_sdiff.mp hj₀).2
    have hle : s j₀ ≤ s i₀ := hS.2 i₀ hi₀S j₀ hj₀S
    calc ∑ i ∈ T \ S, s i ≤ (T \ S).card • s j₀ :=
          Finset.sum_le_card_nsmul _ _ _ (fun x hx => hj₀max x hx)
      _ = (S \ T).card • s j₀ := by rw [hdiff]
      _ ≤ (S \ T).card • s i₀ := by
          simp only [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      _ ≤ ∑ i ∈ S \ T, s i :=
          Finset.card_nsmul_le_sum _ _ _ (fun x hx => hi₀min x hx)
