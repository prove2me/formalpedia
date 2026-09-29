-- Prove2me | solution 1 for F1Tightness.scanCost_lt_baseCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:53.774918+00:00
-- url     : https://prove2.me/submissions/fa530953-4ac4-46f0-acf6-72ea96dec809

-- Sol generated from Probability/F1TightnessCore.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Theorems.Thm_F1Tightness_sum_pairs_identity
import Theorems.Thm_F1Tightness_sum_rank_weights

/-!
# F1 tightness: the slack factor of the master speed-up inequality (paper 250)

This file formalises the *shape layer* of the round-92 "F1-TIGHTNESS-CONNECTION"
deliverable.  The empirical situation is the following.  A scan visits the `M`
cells of a window one after another; the target sits in cell `i` with prior
probability `p i` (the measured **positional profile**, front-loaded, harmonic).
A *policy* is a permutation `σ` of the cells: it probes cell `i` at rank
`σ i + 1`, so its expected probe count is `polCost p σ = ∑ i, (σ i + 1) * p i`.

Three costs organise everything:

* `scanCost p` — the cost of the **ascending** (identity) policy;
* `revCost p`  — the cost of the **descending** (reversed) policy;
* `baseCost M = (M+1)/2` — the cost under a flat profile / random order.

The F1 master inequality of paper 225 reads `S ≤ 1/(Λ·Θ·q̂)`.  On this pool the
parameters are the *cost ratios*

  `Lam p = scanCost / revCost`,   `Theta p = scanCost / baseCost`,   `q̂ = 1`,

and the realizable ascending speed-up is `Sasc p = revCost / scanCost = 1/Λ`.

Main results.

* `scanCost_add_revCost_eq` — the **conservation identity** `c_asc + c_desc = M+1
  = 2·C₀`.  Everything below follows from this single identity: the whole
  parameter map is a one-parameter family.
* `gapX_eq_gapOfLam`, `Theta_eq_of_Lam` — `X = (1+Λ)/(2Λ)` and `Θ = 2Λ/(1+Λ)`
  exactly (no continuum approximation), so `X = 1/Θ`.
* `slack_identity` — `bound = X · S_asc`: the gap between the proven bound and
  the realizable ascending speed-up is exactly the factor `X`, *policy- and
  baseline-independent*.
* `policy_speedup_le_Sasc` — rearrangement: on an antitone (front-loaded)
  profile no policy beats the ascending scan, so `S_asc` is the best realizable
  speed-up.
* `scanCost_lt_baseCost` / `one_lt_gapX` — **strict slack from non-flatness**:
  an antitone profile that is not flat has `X > 1` strictly (a strict Chebyshev
  inequality, proved here from a pairwise identity).
* `no_policy_attains_bound`, `speedup_lt_bound` — consequently *no* realizable
  policy attains the master bound; every policy's speed-up is at most
  `bound / X < bound`.
* `gapX_eq_one_iff`, `gapX_flat` — equality `X = 1` happens exactly when the
  ascending cost equals the flat baseline, in particular for the flat profile;
  this is the equality case that the three independent tests (KS, LRT,
  conditional-logistic LRT) refute on the measured pool.
* `qhat_nonidentifiable`, `anchor_inversion_tautology` — the
  **tightness-circularity catch**: with `q̂` free, *any* observed speed-up can be
  turned into an exact equality, so an anchor whose parameters were obtained by
  inverting the law carries zero evidential weight for attainment.
* Numerical corollaries (`measured_gapX_approx`, `gapX_mem_interval`,
  `measured_bound_approx`, `predicted_speedup_lt_bound`) reproduce the booked
  numbers `Λ = 0.765671`, `Θ ≈ 0.867`, `X ≈ 1.15302 ∈ [1.10, 1.23]`,
  `S ≈ 1.306`, `bound ≈ 1.506`.
-/

open Finset

open F1Tightness

/-! ## A pairwise identity and a strict Chebyshev inequality -/

variable {ι : Type*}


/-- Chebyshev's sum inequality with a strict conclusion: if all pairwise
products are nonpositive and at least one is strictly negative, then
`#s · ∑ a·b < (∑ a)(∑ b)`. -/
theorem card_mul_sum_lt_sum_mul_sum (s : Finset ι) (a b : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, (a i - a j) * (b i - b j) ≤ 0)
    {i₀ j₀ : ι} (hi₀ : i₀ ∈ s) (hj₀ : j₀ ∈ s)
    (hlt : (a i₀ - a j₀) * (b i₀ - b j₀) < 0) :
    (s.card : ℝ) * (∑ i ∈ s, a i * b i) < (∑ i ∈ s, a i) * (∑ i ∈ s, b i) := by
  have hprod : ∑ x ∈ s ×ˢ s, (a x.1 - a x.2) * (b x.1 - b x.2) < 0 := by
    have hzero : ∑ _x ∈ s ×ˢ s, (0 : ℝ) = 0 := by simp
    rw [← hzero]
    refine Finset.sum_lt_sum ?_ ⟨(i₀, j₀), Finset.mem_product.2 ⟨hi₀, hj₀⟩, hlt⟩
    intro x hx
    exact h x.1 (Finset.mem_product.1 hx).1 x.2 (Finset.mem_product.1 hx).2
  rw [Finset.sum_product, sum_pairs_identity] at hprod
  linarith

/-! ## Costs of a scan policy -/

variable {M : ℕ}












/-! ## The conservation identity and positivity -/











/-! ## The identity chain -/






/-! ## The mean-position form of the identity chain -/




/-! ## Monotonicity of the gap factor in `Λ` -/




/-! ## Rearrangement: the ascending policy is optimal on a front-loaded profile -/



/-! ## Strict slack: an antitone non-flat profile cannot attain the bound -/








/-! ## The tightness-circularity catch: `q̂` is not identified -/




/-! ## The measured profile: numerical corollaries -/









open F1Tightness in
theorem solution{p : Fin M → ℝ} (hsum : ∑ i : Fin M, p i = 1)
    (hanti : Antitone p) {i₀ j₀ : Fin M} (hne : p i₀ ≠ p j₀) :
    scanCost p < baseCost M := by
  set a : Fin M → ℝ := fun i => ((i : ℕ) : ℝ) + 1 with ha
  have hmono : ∀ i j : Fin M, i ≤ j → a i ≤ a j := by
    intro i j hij
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
      exact_mod_cast Fin.le_iff_val_le_val.mp hij
    simp only [ha]; linarith
  have hterm : ∀ i ∈ (univ : Finset (Fin M)), ∀ j ∈ (univ : Finset (Fin M)),
      (a i - a j) * (p i - p j) ≤ 0 := by
    intro i _ j _
    rcases le_total i j with hij | hij
    · have h1 : a i - a j ≤ 0 := by linarith [hmono i j hij]
      have h2 : 0 ≤ p i - p j := by linarith [hanti hij]
      nlinarith
    · have h1 : 0 ≤ a i - a j := by linarith [hmono j i hij]
      have h2 : p i - p j ≤ 0 := by linarith [hanti hij]
      nlinarith
  have hstrict : ∃ i ∈ (univ : Finset (Fin M)), ∃ j ∈ (univ : Finset (Fin M)),
      (a i - a j) * (p i - p j) < 0 := by
    rcases lt_trichotomy i₀ j₀ with h | h | h
    · refine ⟨i₀, mem_univ _, j₀, mem_univ _, ?_⟩
      have h1 : a i₀ < a j₀ := by
        have : ((i₀ : ℕ) : ℝ) < ((j₀ : ℕ) : ℝ) := by exact_mod_cast h
        simp only [ha]; linarith
      have h3 : p j₀ < p i₀ := lt_of_le_of_ne (hanti h.le) (Ne.symm hne)
      nlinarith
    · exact absurd (congrArg p h) hne
    · refine ⟨j₀, mem_univ _, i₀, mem_univ _, ?_⟩
      have h1 : a j₀ < a i₀ := by
        have : ((j₀ : ℕ) : ℝ) < ((i₀ : ℕ) : ℝ) := by exact_mod_cast h
        simp only [ha]; linarith
      have h3 : p i₀ < p j₀ := lt_of_le_of_ne (hanti h.le) hne
      nlinarith
  obtain ⟨i, hi, j, hj, hij⟩ := hstrict
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact absurd i₀.isLt (by simp))
  have key := card_mul_sum_lt_sum_mul_sum (univ : Finset (Fin M)) a p hterm hi hj hij
  rw [sum_rank_weights, hsum, Finset.card_univ, Fintype.card_fin] at key
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcost : scanCost p = ∑ i : Fin M, a i * p i := by simp only [scanCost, ha]
  rw [baseCost, hcost]
  nlinarith [key]
