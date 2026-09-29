-- Prove2me | solution 1 for BerggrenHarmonic.expected_surprisal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:11.553913+00:00
-- url     : https://prove2.me/submissions/d13dd16b-08f0-45f6-8adf-28cdb1a9e0b0

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



lemma shannon_eq_sum_surp (P : ProbVec) : shannon P = ∑ a, P.p a * surp P a := by
  unfold shannon surp
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring










/-! ## Cylinder masses in the reals -/





/-! ## The exact level-`n` entropy identity -/

/-- An auxiliary product identity: singling out one factor. -/
lemma prod_ite_mul_single {n : ℕ} (i : Fin n) (f g : Fin n → ℝ) :
    ∏ j, (if j = i then f j * g j else f j) = (∏ j, f j) * g i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i), if_pos rfl,
    Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
  ring


/-! ## Shannon–McMillan–Breiman on the Berggren boundary -/










/-! ## Dimension -/









open BerggrenHarmonic in
theorem solution(P : ProbVec) (n : ℕ) :
    ∑ w : Fin n → Letter, (∏ i, P.p (w i)) * (-Real.log (∏ i, P.p (w i)))
      = n * shannon P := by
  classical
  have hlog : ∀ w : Fin n → Letter,
      -Real.log (∏ i, P.p (w i)) = ∑ i, surp P (w i) := by
    intro w
    rw [Real.log_prod (fun i _ => (P.pos (w i)).ne'), ← Finset.sum_neg_distrib]
    rfl
  have hexp : ∀ w : Fin n → Letter,
      (∏ i, P.p (w i)) * (-Real.log (∏ i, P.p (w i)))
        = ∑ i, (∏ j, P.p (w j)) * surp P (w i) := by
    intro w
    rw [hlog w, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun w _ => hexp w), Finset.sum_comm]
  have hone : ∀ i : Fin n,
      ∑ w : Fin n → Letter, (∏ j, P.p (w j)) * surp P (w i) = shannon P := by
    intro i
    have hfac : ∀ w : Fin n → Letter,
        (∏ j, P.p (w j)) * surp P (w i)
          = ∏ j, (if j = i then P.p (w j) * surp P (w j) else P.p (w j)) := by
      intro w
      exact (prod_ite_mul_single i (fun j => P.p (w j)) (fun j => surp P (w j))).symm
    rw [Finset.sum_congr rfl (fun w _ => hfac w)]
    have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Letter))
      (fun (j : Fin n) (a : Letter) => if j = i then P.p a * surp P a else P.p a)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    have hprod : ∀ j : Fin n,
        (∑ a : Letter, if j = i then P.p a * surp P a else P.p a)
          = if j = i then shannon P else 1 := by
      intro j
      by_cases hj : j = i
      · subst hj
        have hall : ∀ a : Letter,
            (if j = j then P.p a * surp P a else P.p a) = P.p a * surp P a :=
          fun a => if_pos rfl
        rw [Finset.sum_congr rfl (fun a _ => hall a), if_pos rfl, shannon_eq_sum_surp]
      · have hall : ∀ a : Letter, (if j = i then P.p a * surp P a else P.p a) = P.p a :=
          fun a => if_neg hj
        rw [Finset.sum_congr rfl (fun a _ => hall a), if_neg hj]
        exact P.sum_eq
    rw [Finset.prod_congr rfl (fun j _ => hprod j)]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hone i)]
  simp [mul_comm]
