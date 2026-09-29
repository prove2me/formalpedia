-- Prove2me | Definitions.Def_Applications_NET73ConcentrationSpectrum
-- name    : Applications_NET73ConcentrationSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:12.014782+00:00
-- url     : https://prove2.me/theorems/26b635ee-3f1f-47f0-bce2-376ca3eb52e1
-- title:
--   Aether Catalog definitions — Applications_NET73ConcentrationSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NET73ConcentrationSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NET73ConcentrationSpectrum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
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

namespace Catalog.NET73

open Finset AttentionProfile

/-! ## 1. Domains presented by a sorted attention mass vector -/

/-- A domain presented by its attention mass vector, sorted in nonincreasing
order and supported on the first `N` keys. -/
structure MassVector where
  /-- Mass carried by the `i`-th heaviest key. -/
  p : ℕ → ℚ
  /-- Number of keys carrying mass. -/
  N : ℕ
  nonneg : ∀ i, 0 ≤ p i
  sorted : Antitone p
  vanishing : ∀ i, N ≤ i → p i = 0
  total : ∑ i ∈ range N, p i = 1

namespace MassVector

variable (M : MassVector)

/-- Mass captured by the `k` heaviest keys. -/
def cumMass (k : ℕ) : ℚ := ∑ i ∈ range k, M.p i

lemma cumMass_mono : Monotone M.cumMass := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
    (fun i _ _ => M.nonneg i)

lemma cumMass_N : M.cumMass M.N = 1 := M.total

lemma cumMass_le_one (k : ℕ) : M.cumMass k ≤ 1 := by
  rcases le_total k M.N with h | h
  · rw [← M.cumMass_N]; exact M.cumMass_mono h
  · refine le_of_eq ?_
    rw [← M.cumMass_N]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr h) ?_).symm
    intro i _ hi
    exact M.vanishing i (by simpa using hi)

/-- The attention profile of a mass vector, carrying an arbitrary tokenizer
density `d` (the density is a free label: see `tpw_knee_decoupled`). -/
noncomputable def toProfile (d : ℚ) : AttentionProfile where
  tpw := d
  cum := M.cumMass
  cum_zero := by simp [cumMass]
  cum_mono := M.cumMass_mono
  cum_le_one := M.cumMass_le_one
  approaches_one := fun σ hσ => ⟨M.N, by rw [M.cumMass_N]; exact hσ.le⟩


/-- The collision index `S = ∑ p i ^ 2`; `1 / S` is the effective number of
participating keys. -/
def collision : ℚ := ∑ i ∈ range M.N, M.p i ^ 2






end MassVector

/-! ## 2. A worked domain: four equally weighted keys -/

/-- The domain whose attention is spread evenly over four keys. -/
noncomputable def quadUniform : MassVector where
  p := fun i => if i < 4 then 1/4 else 0
  N := 4
  nonneg := by
    intro i
    by_cases h : i < 4 <;> simp [h]
  sorted := by
    intro a b hab
    by_cases hb : b < 4
    · have ha : a < 4 := lt_of_le_of_lt hab hb
      simp [ha, hb]
    · simp only [hb, if_false]
      by_cases ha : a < 4 <;> simp [ha]
  vanishing := by intro i hi; simp [Nat.not_lt.mpr hi]
  total := by norm_num [Finset.sum_range_succ]





/-! ## 3. The exactly solvable decay family -/

/-- The geometric domain: the top-`k` keys capture `1 - r ^ k` of the mass, so
`r` is the decay rate of attention within the domain. -/
noncomputable def geometricProfile (d r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    AttentionProfile where
  tpw := d
  cum := fun k => 1 - r ^ k
  cum_zero := by simp
  cum_le_one := by
    intro k
    have : (0 : ℚ) < r ^ k := pow_pos h0 k
    show (1 : ℚ) - r ^ k ≤ 1
    linarith
  cum_mono := by
    intro a b hab
    have hp : r ^ b ≤ r ^ a := pow_le_pow_of_le_one h0.le h1.le hab
    show (1 : ℚ) - r ^ a ≤ 1 - r ^ b
    linarith
  approaches_one := by
    intro σ hσ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℚ) < 1 - σ by linarith) h1
    exact ⟨n, by linarith⟩






end Catalog.NET73


