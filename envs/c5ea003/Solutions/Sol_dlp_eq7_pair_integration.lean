-- Prove2me | solution 1 for dlp_eq7_pair_integration
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T20:35:27.750046+00:00
-- url     : https://prove2.me/submissions/645599e2-6059-4f0d-95ca-9ab8ba25a2d9

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq (7) INTEGRATION combinator,
on the finite Bernoulli pair model.

Source: dlP–MS 1995, §4, eq (6)→(7), p.5 (/tmp/dlp.txt lines 519–558). Eq (6) is the
CONDITIONAL Lemma-2 bound P( 2^k ‖S'‖ ≥ ‖T_{n,k}‖ | G₂ ) ≥ c_k⁻¹ (a.s.); "integrating
over {‖T_{n,k}‖ ≥ t}" (eq 7) yields P( 2^k ‖S'‖ ≥ t ) ≥ c_k⁻¹ · P( ‖T_{n,k}‖ ≥ t ).

On the finite powerset model the conditioning σ-algebra G₂ = the (Ω₁,Ω₂) block, and
"integration" is a `Finset.sum_le_sum` per (Ω₁,Ω₂). This is the PURE measure-free
combinator: if on each pair-fiber the event `Good Ω₁ Ω₂` forces `condBound Ω₁ Ω₂ ≥ c`
for a constant `c ≥ 0`, then summing against the nonneg pair weights gives
`c · bernoulliPairEventProb p Good ≤ bernoulliPairExpectation p condBound`.
-/

theorem solution
    {n1 n2 : Nat} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : ℝ) (hc : 0 ≤ c)
    (condBound : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) → ℝ)
    (Good : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) → Prop)
    (hcond_nonneg : ∀ Ω₁ Ω₂, 0 ≤ condBound Ω₁ Ω₂)
    (hfiber : ∀ Ω₁ Ω₂, Good Ω₁ Ω₂ → c ≤ condBound Ω₁ Ω₂) :
    c * bernoulliPairEventProb p Good ≤ bernoulliPairExpectation p condBound := by
  -- nonnegativity of bernoulli weights when 0 ≤ p ≤ 1
  have hw_nonneg : ∀ (Omega : Finset (Fin n1 × Fin n2)),
      0 ≤ bernoulliObservationWeight p Omega := by
    intro Omega
    unfold bernoulliObservationWeight
    have h1 : (0:ℝ) ≤ 1 - p := by linarith
    positivity
  unfold bernoulliPairEventProb bernoulliPairExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Ω₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Ω₂ _
  by_cases hg : Good Ω₁ Ω₂
  · simp only [hg, if_true]
    have hw1 := hw_nonneg Ω₁
    have hw2 := hw_nonneg Ω₂
    have hfib := hfiber Ω₁ Ω₂ hg
    have hrw1 : c * (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ * 1)
        = (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂) * c := by ring
    rw [hrw1]
    rw [show bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ * condBound Ω₁ Ω₂
        = (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂) * condBound Ω₁ Ω₂ by ring]
    apply mul_le_mul_of_nonneg_left hfib
    positivity
  · simp only [hg, if_false, mul_zero]
    have hw1 := hw_nonneg Ω₁
    have hw2 := hw_nonneg Ω₂
    have := hcond_nonneg Ω₁ Ω₂
    positivity

#print axioms solution
