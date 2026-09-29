-- Prove2me | solution 1 for Catalog.NET73.geometric_domain_shift_at_equal_density
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:18:07.939919+00:00
-- url     : https://prove2.me/submissions/8c4bd9b4-e04a-4abe-8f63-9b7890257434

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














/-! ## 2. A worked domain: four equally weighted keys -/






/-! ## 3. The exactly solvable decay family -/



/-- **Exact solution of the geometric domain.**  Keeping `k` keys suffices
exactly when the residual mass `r ^ k` has fallen below the slack `1 - τ`. -/
theorem kneeAt_geometric_le_iff {d r τ : ℚ} (h0 : 0 < r) (h1 : r < 1)
    (hτ1 : τ < 1) (k : ℕ) :
    (geometricProfile d r h0 h1).kneeAt τ ≤ k ↔ r ^ k ≤ 1 - τ := by
  constructor
  · intro hle
    have hspec := (geometricProfile d r h0 h1).kneeAt_spec hτ1
    have hmono := (geometricProfile d r h0 h1).cum_mono hle
    have : τ ≤ 1 - r ^ k := by
      simpa using le_trans hspec hmono
    linarith
  · intro hr
    exact (geometricProfile d r h0 h1).kneeAt_le (show τ ≤ 1 - r ^ k by linarith)





open Catalog.NET73 in
theorem solution(d : ℚ) :
    (geometricProfile d (1/2) (by norm_num) (by norm_num)).kneeAt (3/4) = 2 ∧
    (geometricProfile d (9/10) (by norm_num) (by norm_num)).kneeAt (3/4) = 14 ∧
    (geometricProfile d (1/2) (by norm_num) (by norm_num)).tpw =
      (geometricProfile d (9/10) (by norm_num) (by norm_num)).tpw := by
  refine ⟨?_, ?_, rfl⟩
  · have hle : (geometricProfile d (1/2) (by norm_num) (by norm_num)).kneeAt (3/4) ≤ 2 := by
      rw [kneeAt_geometric_le_iff (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    have hnot : ¬ (geometricProfile d (1/2) (by norm_num) (by norm_num)).kneeAt (3/4) ≤ 1 := by
      rw [kneeAt_geometric_le_iff (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    omega
  · have hle : (geometricProfile d (9/10) (by norm_num) (by norm_num)).kneeAt (3/4) ≤ 14 := by
      rw [kneeAt_geometric_le_iff (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    have hnot : ¬ (geometricProfile d (9/10) (by norm_num) (by norm_num)).kneeAt (3/4) ≤ 13 := by
      rw [kneeAt_geometric_le_iff (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    omega
