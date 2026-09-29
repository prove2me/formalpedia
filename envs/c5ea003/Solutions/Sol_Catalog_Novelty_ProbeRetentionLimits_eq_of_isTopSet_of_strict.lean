-- Prove2me | solution 1 for Catalog.Novelty.ProbeRetentionLimits.eq_of_isTopSet_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:10:13.306145+00:00
-- url     : https://prove2.me/submissions/083671e7-ac11-476e-a65f-af79865c2504

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
theorem solution{s : ι → ℝ} {B : ℕ} {S T : Finset ι}
    (hTcard : T.card = B) (hstrict : ∀ i ∈ T, ∀ j ∉ T, s j < s i)
    (hS : IsTopSet s B S) : S = T := by
  classical
  have hsub : T ⊆ S := by
    intro i hiT
    by_contra hiS
    have hne : (T \ S).Nonempty := ⟨i, Finset.mem_sdiff.mpr ⟨hiT, hiS⟩⟩
    have hcard : S.card = T.card := by rw [hS.1, hTcard]
    have hne' : (S \ T).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_comm hcard, Finset.card_pos]
      exact hne
    obtain ⟨j, hj⟩ := hne'
    have hjS : j ∈ S := (Finset.mem_sdiff.mp hj).1
    have hjT : j ∉ T := (Finset.mem_sdiff.mp hj).2
    have h1 : s j < s i := hstrict i hiT j hjT
    have h2 : s i ≤ s j := hS.2 j hjS i hiS
    linarith
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hS.1, hTcard])).symm
