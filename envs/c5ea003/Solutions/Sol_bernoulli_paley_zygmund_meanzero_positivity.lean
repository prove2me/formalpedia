-- Prove2me | solution 1 for bernoulli_paley_zygmund_meanzero_positivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T06:28:27.088686+00:00
-- url     : https://prove2.me/submissions/ffdb9de4-c5ed-4dc4-8fbc-938fe421d4f8

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Giné Ch. 3 / de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211),
Proposition 1 (real-valued base case, the Paley–Zygmund positivity step):

  if E ξ = 0 then  P(ξ ≥ 0) ≥ (E|ξ|)² / (4 E ξ²).

On the discrete Bernoulli powerset measure, in product form (no division):

  (E|F|)² ≤ 4 · E[F²] · P(F ≥ 0).

Proof.  Mean-zero gives E[F·1_{F≥0}] = -E[F·1_{F<0}] = E[F⁻], and
E|F| = E[F⁺] + E[F⁻] = 2 E[F·1_{F≥0}]  (since on {F≥0}, F = |F| ≥ 0 and the
mean-zero identity splits the two halves equally).  Then Cauchy–Schwarz on the
probability measure with the indicator g = 1_{F≥0}:
  (E[F·g])² = (E[(F)·(g)])² ≤ E[F²] · E[g²] = E[F²] · P(F ≥ 0)
(using g² = g for an indicator).  Hence
  (E|F|)² = 4 (E[F·g])² ≤ 4 E[F²] · P(F ≥ 0).

This is the Paley–Zygmund lower-tail brick de la Peña Lemma 2 / the lower-bound
proof consumes (Proposition 1), once mean-zero is established for the centered
chaos statistic.
-/

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliExpectation p F = 0 →
    (bernoulliExpectation p (fun Ω => |F Ω|)) ^ 2 ≤
      4 * bernoulliExpectation p (fun Ω => (F Ω) ^ 2) *
        bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by
  intro hp0 hp1 hmean
  classical
  -- weight nonnegativity
  have hw : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω
    unfold bernoulliObservationWeight
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1p _)
  -- indicator of {F ≥ 0}
  set g : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Ω => if 0 ≤ F Ω then (1 : ℝ) else 0 with hg
  -- Mean-zero identity:  E|F| = 2 · E[F·g].
  -- Pointwise:  |F Ω| = 2 * (F Ω * g Ω) - F Ω.
  have hpt : ∀ Ω, |F Ω| = 2 * (F Ω * g Ω) - F Ω := by
    intro Ω
    simp only [hg]
    by_cases h : 0 ≤ F Ω
    · rw [if_pos h, abs_of_nonneg h]; ring
    · have h' : F Ω < 0 := lt_of_not_ge h
      rw [if_neg h, abs_of_neg h']; ring
  -- Therefore  E|F| = 2·E[F·g] − E[F] = 2·E[F·g].
  have hEabs : bernoulliExpectation p (fun Ω => |F Ω|)
      = 2 * bernoulliExpectation p (fun Ω => F Ω * g Ω) := by
    unfold bernoulliExpectation
    have hmean' : ∑ Ω : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Ω * F Ω = 0 := by
      have := hmean; unfold bernoulliExpectation at this; exact this
    calc ∑ Ω, bernoulliObservationWeight p Ω * |F Ω|
        = ∑ Ω, bernoulliObservationWeight p Ω *
            (2 * (F Ω * g Ω) - F Ω) := by
              apply Finset.sum_congr rfl; intro Ω _; rw [hpt Ω]
      _ = ∑ Ω, (2 * (bernoulliObservationWeight p Ω * (F Ω * g Ω))
              - bernoulliObservationWeight p Ω * F Ω) := by
              apply Finset.sum_congr rfl; intro Ω _; ring
      _ = 2 * (∑ Ω, bernoulliObservationWeight p Ω * (F Ω * g Ω))
            - ∑ Ω, bernoulliObservationWeight p Ω * F Ω := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 2 * (∑ Ω, bernoulliObservationWeight p Ω * (F Ω * g Ω)) := by
              rw [hmean']; ring
  -- g is an indicator:  g² = g  and  0 ≤ g.
  have hgnn : ∀ Ω, 0 ≤ g Ω := by
    intro Ω; simp only [hg]; by_cases h : 0 ≤ F Ω <;> simp [h]
  have hgsq : ∀ Ω, (g Ω) ^ 2 = g Ω := by
    intro Ω; simp only [hg]; by_cases h : 0 ≤ F Ω <;> simp [h]
  -- Cauchy–Schwarz:  (E[F·g])² ≤ E[F²]·E[g²]      via  (w·(F·g))² = (w·F²)·(w·g²)
  have hCS :
      (∑ Ω : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * (F Ω * g Ω)) ^ 2 ≤
        (∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * (F Ω) ^ 2) *
          (∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * (g Ω) ^ 2) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
      (fun Ω _ => mul_nonneg (hw Ω) (by positivity))
      (fun Ω _ => ?_)
    -- (w·(F·g))² = (w·F²)·(w·g²)
    ring
  -- E[g²] = E[g] = P(F ≥ 0).
  have hEg : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Ω * (g Ω) ^ 2)
      = bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl
    intro Ω _
    rw [hgsq Ω]; simp only [hg]
    by_cases h : 0 ≤ F Ω <;> simp [h]
  -- Assemble:  (E|F|)² = 4·(E[F·g])² ≤ 4·E[F²]·E[g²] = 4·E[F²]·P(F≥0).
  rw [hEabs]
  have hEFg2 : (2 * bernoulliExpectation p (fun Ω => F Ω * g Ω)) ^ 2
      = 4 * (bernoulliExpectation p (fun Ω => F Ω * g Ω)) ^ 2 := by ring
  rw [hEFg2]
  have hCS' : (bernoulliExpectation p (fun Ω => F Ω * g Ω)) ^ 2 ≤
      bernoulliExpectation p (fun Ω => (F Ω) ^ 2) *
        bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by
    have := hCS
    rw [hEg] at this
    simpa [bernoulliExpectation] using this
  calc 4 * (bernoulliExpectation p (fun Ω => F Ω * g Ω)) ^ 2
      ≤ 4 * (bernoulliExpectation p (fun Ω => (F Ω) ^ 2) *
          bernoulliEventProb p (fun Ω => 0 ≤ F Ω)) := by
        apply mul_le_mul_of_nonneg_left hCS' (by norm_num)
    _ = 4 * bernoulliExpectation p (fun Ω => (F Ω) ^ 2) *
          bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by ring
