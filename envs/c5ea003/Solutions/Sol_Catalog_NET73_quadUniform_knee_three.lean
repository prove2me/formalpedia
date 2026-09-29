-- Prove2me | solution 1 for Catalog.NET73.quadUniform_knee_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:18:08.488301+00:00
-- url     : https://prove2.me/submissions/12395f11-c73b-4ab7-ab2d-acfe1c341c8f

-- Sol generated from Applications/NET73ConcentrationSpectrum.lean
import Mathlib
import Definitions.Def_Applications_NET73ConcentrationSpectrum
import Definitions.Def_Applications_NET73KneeDecoupling
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_le
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_spec
/-
# NET-73, cycle 2: the concentration spectrum of a domain

`Applications/NET73KneeDecoupling.lean` shows that the knee `k*` is a functional
of the attention capture curve and is decoupled from tokens-per-word.  This file
asks the follow-up question the NET-73 verdict poses — *what relational
statistic does control the knee?* — and answers it with two independent bounds
and one exactly solvable family.

* **Participation bound** (`kneeAt_ge_sq_div_collision`).  For a domain whose
  attention mass vector is `p` with collision index `S = ∑ p i ^ 2` (the
  Rényi-2 / inverse-participation statistic), the knee obeys
  `k* ≥ τ² / S`.  The proof is Cauchy–Schwarz on the top-`k` block, so the
  bound is information-theoretic: the effective number of participating keys
  `1/S` lower-bounds (up to `τ²`) how many keys must be kept.
* **Top-mass bound** (`kneeAt_ge_tol_div_top`).  For a sorted mass vector the
  knee is at least `τ / p 0`: a domain with a single dominant key has a small
  knee, no matter how many tokens its words cost.
* **Geometric family** (`kneeAt_geometric_le_iff`).  For the exactly solvable
  decay profile `cum k = 1 - r ^ k` the knee is characterised by
  `k* ≤ k ↔ r ^ k ≤ 1 - τ`, is monotone in the decay rate `r`, and produces
  `geometric_domain_shift_at_equal_density`: two domains with *identical*
  tokens-per-word whose knees are `2` and `14` at the same tolerance — the
  in-model analogue of code (`k* = 12`) versus French (`k* > 32`).

Together these say the domain shift lives on the decay-rate axis, exactly where
NET-73's refutation of tokenization density pushes it.
-/

open Catalog.NET73

open Finset AttentionProfile

/-! ## 1. Domains presented by a sorted attention mass vector -/


open MassVector

variable (M : MassVector)






@[simp] lemma toProfile_cum (d : ℚ) : (M.toProfile d).cum = M.cumMass := rfl








/-! ## 2. A worked domain: four equally weighted keys -/


lemma quadUniform_collision : quadUniform.collision = 1/4 := by
  norm_num [MassVector.collision, quadUniform, Finset.sum_range_succ]

lemma quadUniform_cum_two : quadUniform.cumMass 2 = 1/2 := by
  norm_num [MassVector.cumMass, quadUniform, Finset.sum_range_succ]

lemma quadUniform_cum_three : quadUniform.cumMass 3 = 3/4 := by
  norm_num [MassVector.cumMass, quadUniform, Finset.sum_range_succ]


/-! ## 3. The exactly solvable decay family -/








open Catalog.NET73 in
theorem solution(d : ℚ) :
    (quadUniform.toProfile d).kneeAt (3/4) = 3 ∧
    (3 / 4 : ℚ) ^ 2 / quadUniform.collision ≤ 3 := by
  constructor
  · refine le_antisymm ?_ ?_
    · refine (quadUniform.toProfile d).kneeAt_le ?_
      rw [toProfile_cum, quadUniform_cum_three]
    · by_contra hlt
      push_neg at hlt
      have hle2 : (quadUniform.toProfile d).kneeAt (3/4) ≤ 2 := by omega
      have hspec := (quadUniform.toProfile d).kneeAt_spec (τ := 3/4) (by norm_num)
      have hmono := (quadUniform.toProfile d).cum_mono hle2
      rw [toProfile_cum] at hspec hmono
      rw [quadUniform_cum_two] at hmono
      linarith
  · rw [quadUniform_collision]; norm_num
