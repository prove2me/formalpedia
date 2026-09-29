-- Prove2me | solution 1 for BerggrenHarmonic.shannon_eq_log_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:13.737691+00:00
-- url     : https://prove2.me/submissions/190efcdc-38a2-4991-9d31-eead368588dd

-- Sol generated from Bridges/BerggrenBoundaryEntropy.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenBoundaryEntropy
import Definitions.Def_Bridges_BerggrenHarmonicMeasure

/-!
# Entropy and dimension of the harmonic measure on the Berggren boundary

Building on `Catalog.Bridges.BerggrenHarmonicMeasure`, where the harmonic measure of the
Berggren random walk was identified with the Bernoulli product measure `bernoulli P` on the
3-adic boundary `Bdry = ℕ → Fin 3`, this file computes its **entropy** and its **pointwise
(Billingsley) dimension**.

## Main results

* `shannon` : the Shannon entropy `H(p₁,p₂,p₃) = -∑ pₐ log pₐ` of the step distribution.
* `expected_surprisal` : the *exact* level-`n` identity
  `∑_{w ∈ {1,2,3}ⁿ} μ[w] · (-log μ[w]) = n · H(p)`.  The mean surprisal of a depth-`n`
  cylinder is exactly `n H(p)` — no error term.
* `shannon_le_log_three`, `shannon_eq_log_three_iff` : `H(p) ≤ log 3` with equality exactly
  for the fair walk, so the harmonic measure has full dimension iff the three Berggren moves
  are equally likely.
* `strongLaw_surprisal`, `smb_ae` : the Shannon–McMillan–Breiman theorem for the Berggren
  boundary: `μ`-almost every boundary point `x` satisfies `-(1/n) log μ(cyl n x) → H(p)`.
* `pointwise_dimension_ae` : consequently the pointwise dimension of the harmonic measure
  with respect to the natural 3-adic metric (`diam (cyl n x) = 3⁻ⁿ`) is almost surely the
  constant `dimH P = H(p)/log 3 ∈ (0, 1]`.
* `dim_le_one`, `dim_uniform_eq_one`, `dim_eq_one_iff` : the dimension is at most `1`, the
  dimension of the whole 3-adic Cantor boundary, with equality iff the walk is fair.
-/

open BerggrenHarmonic

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

/-! ## Surprisal and Shannon entropy -/






/-- One term of Gibbs' inequality, via `log t ≤ t - 1`. -/
lemma gibbs_term_le (P : ProbVec) (a : Letter) :
    P.p a * Real.log (1 / (3 * P.p a)) ≤ 1 / 3 - P.p a := by
  have hpa := P.pos a
  have hx : (0:ℝ) < 1 / (3 * P.p a) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  have hid : P.p a * (1 / (3 * P.p a) - 1) = 1 / 3 - P.p a := by field_simp
  nlinarith [hpa]

/-- The strict form of the previous inequality away from the uniform weight. -/
lemma gibbs_term_lt (P : ProbVec) (a : Letter) (h : P.p a ≠ 1 / 3) :
    P.p a * Real.log (1 / (3 * P.p a)) < 1 / 3 - P.p a := by
  have hpa := P.pos a
  have hx : (0:ℝ) < 1 / (3 * P.p a) := by positivity
  have hxne : 1 / (3 * P.p a) ≠ 1 := by
    intro hcon
    apply h
    field_simp at hcon
    linarith
  have hlt := Real.log_lt_sub_one_of_pos hx hxne
  have hid : P.p a * (1 / (3 * P.p a) - 1) = 1 / 3 - P.p a := by field_simp
  nlinarith [hpa]

lemma sum_gibbs_lhs (P : ProbVec) :
    ∑ a, P.p a * Real.log (1 / (3 * P.p a)) = -Real.log 3 + shannon P := by
  have hL : ∀ a : Letter, P.p a * Real.log (1 / (3 * P.p a))
      = P.p a * (-Real.log 3) - P.p a * Real.log (P.p a) := by
    intro a
    have hpa := P.pos a
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hpa)]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hL a), Finset.sum_sub_distrib, ← Finset.sum_mul,
    P.sum_eq, shannon]
  ring

lemma sum_gibbs_rhs (P : ProbVec) : ∑ a : Letter, (1 / 3 - P.p a) = 0 := by
  rw [Finset.sum_sub_distrib, P.sum_eq]
  norm_num




/-! ## Cylinder masses in the reals -/





/-! ## The exact level-`n` entropy identity -/



/-! ## Shannon–McMillan–Breiman on the Berggren boundary -/










/-! ## Dimension -/









open BerggrenHarmonic in
theorem solution(P : ProbVec) :
    shannon P = Real.log 3 ↔ ∀ a, P.p a = 1 / 3 := by
  constructor
  · intro heq
    by_contra hne
    push_neg at hne
    obtain ⟨b, hb⟩ := hne
    have h := Finset.sum_lt_sum (fun a (_ : a ∈ Finset.univ) => gibbs_term_le P a)
      ⟨b, Finset.mem_univ b, gibbs_term_lt P b hb⟩
    rw [sum_gibbs_lhs, sum_gibbs_rhs] at h
    linarith
  · intro h
    unfold shannon
    have hval : ∀ a : Letter, P.p a * Real.log (P.p a) = (1 / 3) * Real.log (1 / 3) := by
      intro a; rw [h a]
    rw [Finset.sum_congr rfl (fun a _ => hval a)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [one_div, Real.log_inv]
    ring
