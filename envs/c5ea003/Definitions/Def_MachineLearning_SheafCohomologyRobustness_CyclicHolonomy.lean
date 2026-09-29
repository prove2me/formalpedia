-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
-- name    : MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T02:34:25.976241+00:00
-- url     : https://prove2.me/theorems/6572927b-c94b-4498-b963-73f2931a2b29
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_CyclicHolonomy
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.CyclicHolonomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/CyclicHolonomy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_Cohomology
import Theorems.Thm_SheafCohomologyRobustness_deltaCyc_sum_zero
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

namespace SheafCohomologyRobustness

variable {n : ℕ}

/-! ## §1. An explicit primitive for zero-holonomy cyclic cochains -/

/-- Discrete primitive of `g` up to index `k`: `∑_{j < k} gⱼ`. -/
noncomputable def partialSum (g : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val < k), g j

lemma partialSum_succ (g : Fin (n + 1) → ℝ) (k : ℕ) (hk : k < n + 1) :
    partialSum g (k + 1) = partialSum g k + g ⟨k, hk⟩ := by
  unfold partialSum
  have hins : (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k + 1))
      = insert (⟨k, hk⟩ : Fin (n + 1))
          (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · simp
      · omega
  have hnot : (⟨k, hk⟩ : Fin (n + 1))
      ∉ (Finset.univ.filter (fun j : Fin (n + 1) => j.val < k)) := by simp
  rw [hins, Finset.sum_insert hnot]
  ring

lemma partialSum_full (g : Fin (n + 1) → ℝ) : partialSum g (n + 1) = ∑ j, g j := by
  unfold partialSum
  congr 1
  ext j
  simpa using j.isLt

/-- **Zero holonomy implies gluing on the loop nerve.**  If the loop sum of the
overlap discrepancy `g` vanishes, the discrete primitive `k ↦ ∑_{j<k} gⱼ` is a
global potential for `g`, wrap-around included. -/
theorem deltaCyc_of_sum_zero (g : Fin (n + 1) → ℝ) (hg : ∑ i, g i = 0) :
    deltaCyc (fun k => partialSum g k.val) = g := by
  funext i
  simp only [deltaCyc]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
  · have hsucc : (i + 1 : Fin (n + 1)).val = i.val + 1 := by
      rw [Fin.val_add_one_of_lt]
      exact Fin.lt_def.mpr (by simpa using hi)
    rw [hsucc, partialSum_succ g i.val i.isLt]
    simp
  · have hlast : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.val_add, ← hi]
    rw [hlast]
    have h0 : partialSum g (0 : Fin (n + 1)).val = 0 := by simp [partialSum]
    rw [h0, hi]
    have hkey := partialSum_succ g n (by omega)
    rw [partialSum_full, hg] at hkey
    have hin : (⟨n, by omega⟩ : Fin (n + 1)) = i := Fin.ext hi.symm
    rw [hin] at hkey
    linarith

/-- **The loop obstruction is exactly the holonomy.**  A cyclic overlap
discrepancy is a coboundary iff its total loop sum vanishes. -/
theorem isCoboundary_iff_holonomy_zero (g : Fin (n + 1) → ℝ) :
    (∃ f, deltaCyc f = g) ↔ ∑ i, g i = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact deltaCyc_sum_zero f
  · intro hg
    exact ⟨_, deltaCyc_of_sum_zero g hg⟩

/-! ## §2. `H¹` of the loop nerve is one-dimensional -/

/-- The cyclic coboundary operator as an `ℝ`-linear map. -/
def deltaCycL (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := deltaCyc
  map_add' f g := by
    funext i; simp only [deltaCyc, Pi.add_apply]; ring
  map_smul' a f := by
    funext i; simp only [deltaCyc, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

/-- The holonomy (total loop sum) as an `ℝ`-linear functional on `1`-cochains. -/
def holonomyL (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∑ i, g i
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum]

/-- **Cocycles modulo coboundaries.**  The image of the cyclic coboundary is
precisely the kernel of the holonomy functional. -/
theorem range_deltaCycL_eq_ker_holonomy (n : ℕ) :
    LinearMap.range (deltaCycL n) = LinearMap.ker (holonomyL n) := by
  ext g
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact isCoboundary_iff_holonomy_zero g

theorem holonomyL_surjective (n : ℕ) : Function.Surjective (holonomyL n) := by
  intro r
  refine ⟨fun _ => r / (n + 1), ?_⟩
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  show ∑ _i : Fin (n + 1), r / (n + 1) = r
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- **`H¹` of the loop nerve is canonically `ℝ`, via the holonomy.**  The first
cohomology of the cyclic nerve with real coefficients is one-dimensional, and the
isomorphism to `ℝ` is induced by the loop sum: two overlap discrepancies are
cohomologous iff they have the same holonomy. -/
noncomputable def cyclicH1EquivReal (n : ℕ) :
    ((Fin (n + 1) → ℝ) ⧸ LinearMap.range (deltaCycL n)) ≃ₗ[ℝ] ℝ :=
  (Submodule.quotEquivOfEq _ _ (range_deltaCycL_eq_ker_holonomy n)).trans
    ((holonomyL n).quotKerEquivOfSurjective (holonomyL_surjective n))



/-! ## §3. The quantitative defect theorem -/





end SheafCohomologyRobustness


