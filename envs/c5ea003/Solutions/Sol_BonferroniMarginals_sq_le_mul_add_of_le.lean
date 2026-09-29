-- Prove2me | solution 1 for BonferroniMarginals.sq_le_mul_add_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:21:01.599344+00:00
-- url     : https://prove2.me/submissions/e91b11dc-9529-4622-b9bf-0feb80be4b4e

-- Sol generated from MachineLearning/BonferroniMarginals/Corradi.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity

/-!
# Which marginals? The Corrádi bound and the Fisher-type consequence

`Core.lean` develops the Bonferroni machinery for an *arbitrary* finite family;
the content of the conjecture is therefore entirely in **which marginals are fed
into it**.  This file feeds in the two standard hypotheses of design theory and
of ensemble learning:

* a uniform lower bound `m ≤ |Aᵢ|` on the **first** marginals, and
* a uniform upper bound `|Aᵢ ∩ Aⱼ| ≤ t` (`i ≠ j`) on the **second** marginals,

and extracts the sharp conclusions.

Main results.

* `card_cover_corradi` — **Corrádi's inequality**, division-free:
  `k·m² ≤ |cover| · (m + (k−1)·t)`, where `k` is the number of sets.
  Equivalently `|⋃ᵢ Aᵢ| ≥ k m² / (m + (k−1) t)`.
* `fisher_type_bound` — turning the same data around: if the ambient union is
  small (`N·t < m²`) then the *number of sets* is bounded,
  `k · (m² − N·t) ≤ N · (m − t)`.  This is the counting principle behind Fisher's
  inequality and behind Plotkin-type bounds in coding theory.
* `corradi_tight_of_pairwiseDisjoint`, `corradi_tight_of_constant` — the bound is
  attained at *both* extremes of the correlation scale (`t = 0` partitions and
  `t = m` totally correlated families), so no better bound is expressible in the
  marginal data `(k, m, t)` alone.
* `ensemble_coverage_bound` — the machine-learning reading: `k` hypotheses each
  failing on at least `m` of `N` samples, with pairwise co-failure at most `t`,
  must jointly fail on many distinct samples.

The proof route is: `sq_sum_card_le_card_cover_mul_sum_prod` (Cauchy–Schwarz on
the multiplicity function) + monotonicity of `S ↦ S²/(S+c)` + the marginal
hypotheses.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-! ## Two arithmetic lemmas -/



/-! ## Corrádi's inequality -/



/-! ## Sharpness at both ends of the correlation scale -/



/-! ## The machine-learning corollary -/




open BonferroniMarginals in
theorem solution{N S u c : ℕ} (h : S ^ 2 ≤ N * (S + c)) (hu : u ≤ S) :
    u ^ 2 ≤ N * (u + c) := by
  rcases Nat.eq_zero_or_pos (S + c) with hSc | hSc
  · have hS : S = 0 := by omega
    have hu0 : u = 0 := by omega
    have hc : c = 0 := by omega
    simp [hu0, hc]
  · -- work in `ℤ` and multiply the goal by the positive number `S + c`
    by_contra hcon
    push_neg at hcon
    have hZ : (N : ℤ) * (u + c) + 1 ≤ (u : ℤ) ^ 2 := by exact_mod_cast hcon
    have hZ' : (S : ℤ) ^ 2 ≤ (N : ℤ) * ((S : ℤ) + c) := by exact_mod_cast h
    have huS : (u : ℤ) ≤ S := by exact_mod_cast hu
    have hSc' : (0 : ℤ) < (S : ℤ) + c := by exact_mod_cast hSc
    have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
    have hc0 : (0 : ℤ) ≤ c := Int.natCast_nonneg c
    nlinarith [mul_nonneg (mul_nonneg hu0 (le_trans hu0 huS)) (sub_nonneg.mpr huS),
      mul_nonneg hc0 (mul_nonneg (sub_nonneg.mpr huS) (add_nonneg hu0 (le_trans hu0 huS))),
      mul_le_mul_of_nonneg_left hZ' (add_nonneg hu0 hc0)]
