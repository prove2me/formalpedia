-- Prove2me | Definitions.Def_Bridges_GL3TropicalSatakeCertification
-- name    : Bridges_GL3TropicalSatakeCertification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:53.889993+00:00
-- url     : https://prove2.me/theorems/2326a6b8-aa01-44c6-ba31-262886fd95b3
-- title:
--   Aether Catalog definitions — Bridges_GL3TropicalSatakeCertification
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3TropicalSatakeCertification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3TropicalSatakeCertification.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# GL₃ Tropical Satake Certified Robustness for Top-2 Gap Hecke-Score Classifiers

This file establishes a direct multiclass certification theorem for tropical GL₃
Hecke-score classifiers using the gap between the largest and second-largest scores.

## Overview

The key mathematical insight is that **argmax stability under perturbation** reduces to a
clean quantitative estimate: the difference of any two score functions changes by at most
`2 * C * ‖δ‖∞` when the individual scores are each `C`-Lipschitz in `L∞`. From this single
estimate, all certification theorems follow by elementary reasoning.

## Main Results

### Abstract score-family API

* `ScoreLipschitzInf` — uniform `L∞`-Lipschitz bound on a family of score functions
* `IsTopClass` — weak winner predicate (∀ j, s j x ≤ s i x)
* `IsUniqueTopClass` — strict winner predicate (unique argmax)
* `top2Gap` — margin of a class against competitors via `Finset.sup'`

### Core quantitative lemmas

* `score_diff_le_two_mul_lipschitz` — the essential perturbation estimate:
  `|(s i x - s j x) - (s i y - s j y)| ≤ 2 * C * ‖x - y‖∞`
* `score_gap_positive_under_perturbation` — strict gap preservation under perturbation

### Certification theorems

* `unique_top_stable_of_inf_margin` — unique argmax is preserved when the pairwise
  margin exceeds `2 * C * ‖δ‖∞` for all competitors
* `unique_top_certified_radius'` — radius-form certification with explicit radius `r`
* `unique_top_certified_radius_Kd` — specialization with Lipschitz constant `K * d`
* `top2Gap_pos_iff_unique_top` — the top-2 gap characterizes unique winners
* `unique_top_stable_of_top2Gap` — the cleanest certification: perturbation radius
  is `top2Gap / (2 * K * d)`

## Design

The development cleanly separates two layers:
1. **Robustness layer** (this file): converts any uniform Lipschitz bound into certified
   invariance of argmax under `L∞` perturbations.
2. **Representation-theoretic layer** (future): establishes Lipschitz control for specific
   GL₃ Hecke/Satake score constructions.

The abstract API works for any `Fin m`-indexed family of score functions and immediately
supports top-k stability, abstaining classifiers, and extensions beyond GL₃.

## References

* Tropical geometry and neural network robustness via the Satake isomorphism
* Certified adversarial robustness via randomized smoothing (Cohen et al., 2019)
* Lipschitz-margin training (Tsuzuku et al., 2018)
-/

open Finset

noncomputable section

/-! ## Core Definitions -/

/-- A family of score functions `s : Fin m → (Fin d → ℝ) → ℝ` is **uniformly Lipschitz
with constant `C`** in the `L∞` norm if every individual score satisfies
`|s i x - s i y| ≤ C * ‖x - y‖∞`. -/
def ScoreLipschitzInf {m d : ℕ} (C : ℝ) (s : Fin m → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ i x y, |s i x - s i y| ≤ C * ‖x - y‖


/-- Class `i` is a **top class** (weak winner) at input `x` if its score is at least
as large as every other class's score. -/
def IsTopClass {m d : ℕ} (s : Fin m → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin m) : Prop :=
  ∀ j, s j x ≤ s i x

/-- Class `i` is the **unique top class** (strict winner) at input `x` if its score
strictly dominates every other class's score. -/
def IsUniqueTopClass {m d : ℕ} (s : Fin m → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    Prop :=
  (∀ j, s j x ≤ s i x) ∧ ∀ j, j ≠ i → s j x < s i x

/-- The **top-2 gap** of class `i` at input `x`: the score of `i` minus the maximum
score among all competitors. This equals the margin between the predicted class and the
runner-up. Requires `1 < m` so that competitors exist. -/
private lemma erase_univ_nonempty {m : ℕ} [Fact (1 < m)] (i : Fin m) :
    (Finset.univ.erase i).Nonempty := by
  have hm : 1 < m := Fact.out
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩

def top2Gap {m d : ℕ} [Fact (1 < m)] (s : Fin m → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (i : Fin m) : ℝ :=
  s i x - Finset.sup' (Finset.univ.erase i) (erase_univ_nonempty i) (fun j => s j x)

/-! ## The Key Quantitative Estimate -/

/-
**Two-score perturbation bound.** The difference of two scores changes by at most
`2 * C * ‖x - y‖∞` under perturbation. This is the essential quantitative estimate
from which all certification results follow.

The proof rewrites `(s i x - s j x) - (s i y - s j y)` as
`(s i x - s i y) - (s j x - s j y)` and uses the triangle inequality together
with both Lipschitz bounds.
-/

/-
**Strict gap preservation.** If the score gap `s i x - s j x` exceeds `2 * C * ‖δ‖∞`,
then `s i` still strictly dominates `s j` at the perturbed input `x + δ`.

The proof obtains a lower bound
`s i (x+δ) - s j (x+δ) ≥ (s i x - s j x) - 2*C*‖δ‖∞ > 0`
from the two-score perturbation bound.
-/

/-! ## Main Certification Theorems -/

/-
**Argmax stability (weak form).** If `i` is the unique top class at `x` and
every pairwise margin exceeds `2 * C * ‖δ‖∞`, then `i` is a top class at `x + δ`.
-/

/-
**Unique argmax stability.** The strict winner is preserved under perturbation.
This is the main abstract certification theorem.
-/

/-! ## Radius-Form Certification -/

/-
**Radius-form certification.** If `‖δ‖∞ < r` and every pairwise margin exceeds
`2 * C * r`, then the unique argmax is preserved. This is the most reusable API:
instantiate `r = gap / (2*C)` to get the top-2 gap theorem.
-/

/-
**Radius-form with `K * d` constant.** Specialization for tropical degree scaling
where the Lipschitz constant is `K * d` rather than a single `C`.
-/

/-! ## Top-2 Gap Characterization -/

/-
The top-2 gap is positive if and only if the class is a strict (unique) winner.
-/

/-! ## The Clean Top-2 Gap Certification -/

/-
**Top-2 gap certification with `K * d` Lipschitz constant.**
This is the cleanest formal expression of the certified robustness statement:
the predicted class is stable whenever `‖δ‖∞ < top2Gap / (2 * K * d)`.

This theorem directly certifies multiclass GL₃ tropical Hecke-score classifiers:
given the verified Lipschitz bound from the representation-theoretic layer, the
certification radius is computed from a single evaluation of the score functions.
-/

end


