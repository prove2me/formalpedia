-- Prove2me | solution 1 for SheafCohomologyRobustness.cyclic_defect_attained
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:08:50.507512+00:00
-- url     : https://prove2.me/submissions/3c3f17ea-9d03-41be-adbe-3c428fd65474

-- Sol generated from MachineLearning/SheafCohomologyRobustness/CyclicHolonomy.lean
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_Cohomology
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Exact Computation of `H¹` of the Loop Nerve, and the Quantitative Defect Theorem

`SheafCohomologyRobustness.Cohomology` proved that the cyclic (loop) nerve has
*nonvanishing* first cohomology, by exhibiting one non-coboundary.  This file
computes the cohomology **exactly** and extracts the resulting quantitative
certified-robustness statement.

Main results.

* `deltaCyc_of_sum_zero` / `isCoboundary_iff_holonomy_zero` — a cyclic overlap
  discrepancy `g` glues **iff** its holonomy `∑ᵢ gᵢ` vanishes.  Together with
  `Cohomology.deltaCyc_sum_zero` this identifies the coboundaries with the
  hyperplane `{∑ g = 0}`.
* `range_deltaCycL_eq_ker_holonomy` — the same statement as an equality of
  submodules, `range δ_cyc = ker(holonomy)`.
* `cyclicH1EquivReal`, `finrank_cyclicH1` — hence
  `H¹(loop nerve, ℝ) ≃ₗ[ℝ] ℝ` and `dim H¹ = 1`: the holonomy is a *complete*
  invariant of the cohomology class, so the loop nerve carries exactly one
  independent adversarial obstruction.
* `cyclic_defect_lower_bound` / `cyclic_defect_attained` /
  `cyclic_defect_isLeast` — the **quantitative defect theorem**: the best
  uniform approximation of `g` by a coboundary has error exactly
  `|∑ᵢ gᵢ| / (n+1)`.  Cohomology is thereby given a metric meaning: the size of
  the obstruction class is the unavoidable certificate mismatch.
* `holonomy_forces_certificate_gap` — consequently, a loop of `n+1` regions with
  holonomy `H` admits **no** global certificate assignment whose per-overlap
  mismatch is smaller than `|H| / (n+1)`: an explicit adversarial witness scale.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): "`H¹` of a loop is one-dimensional, and its class
  has a *metric* meaning: the norm of the class equals the smallest achievable
  uniform certificate mismatch, `|holonomy|/(number of regions)`."
* Experiment (Experimenter): the potential `f k = ∑_{j < k} g j` works verbatim
  for the cyclic nerve *provided* the loop sum vanishes; the wrap-around index
  `n ↦ 0` is the only case needing the hypothesis, and it is exactly where the
  holonomy is consumed (`deltaCyc_of_sum_zero`, second branch).
* Analysis (Analyst): the lower bound `|∑ g| ≤ (n+1) ε` is a pure averaging /
  triangle-inequality argument, and it is *tight* because the constant cochain
  `(∑ g)/(n+1)` realises it — the extremal cochain is the harmonic (constant)
  representative of the class.  This is the discrete Hodge-theoretic statement:
  each class has a unique constant representative of minimal sup-norm.
* Critique (Critic): the defect statement is stated as `IsLeast`, so it is not
  an unattained infimum; both bounds are proved, and the `n = 0` corner case
  (single region, self-loop) is covered since `(n : ℝ) + 1 > 0` always.
* Synthesis (PI): with `GraphNervePoincare.discrete_poincare_lemma` (qualitative,
  arbitrary nerve) plus this file (quantitative, loop nerve) the cohomological
  robustness ledger is complete for `1`-dimensional nerves.
-/


open BigOperators Finset

open SheafCohomologyRobustness

variable {n : ℕ}

/-! ## §1. An explicit primitive for zero-holonomy cyclic cochains -/






/-! ## §2. `H¹` of the loop nerve is one-dimensional -/








/-! ## §3. The quantitative defect theorem -/






open SheafCohomologyRobustness in
theorem solution(g : Fin (n + 1) → ℝ) :
    ∃ f, ∀ i, |deltaCyc f i - g i| = |∑ j, g j| / ((n : ℝ) + 1) := by
  set H := ∑ j, g j with hH
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  set g' : Fin (n + 1) → ℝ := fun i => g i - H / ((n : ℝ) + 1) with hg'
  have hzero : ∑ i, g' i = 0 := by
    simp only [hg', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    rw [hH]
    push_cast
    ring
  obtain ⟨f, hf⟩ : ∃ f, deltaCyc f = g' := ⟨_, deltaCyc_of_sum_zero g' hzero⟩
  refine ⟨f, fun i => ?_⟩
  rw [hf]
  have : g' i - g i = - (H / ((n : ℝ) + 1)) := by simp [hg']
  rw [this, abs_neg, abs_div]
  congr 1
  have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [abs_of_nonneg this]
