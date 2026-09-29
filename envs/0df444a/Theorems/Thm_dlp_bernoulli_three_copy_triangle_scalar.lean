-- Prove2me | Theorems.Thm_dlp_bernoulli_three_copy_triangle_scalar
-- name    : dlp_bernoulli_three_copy_triangle_scalar
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T17:51:04.763005+00:00
-- url     : https://prove2.me/theorems/f4a6a5f0-e3c7-4db1-9ed4-27fce481e8dc
-- statement:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) Lemma 1, transported to the finite Bernoulli powerset probability model. For any scalar statistic Z on the sampling set and any threshold t: P(t ≤ |Z(Ω)|) ≤ 3·P(2t/3 ≤ |Z(Ω₁)+Z(Ω₂)|), where the LHS is the single-copy bernoulliEventProb and the RHS is the decoupled three-copy bernoulliTripleEventProb (the third copy does not appear in the event). Stated with absolute values on both sides to faithfully match Lemma 1 at the scalar instance V=ℝ (where ‖r‖=|r|); the signed/ordered variant is false because the union-cover in Lemma 1's proof genuinely needs the norm/triangle inequality 2X=(X+Y)+(X+Z)−(Y+Z). This is the matrix→scalar 3-copy desymmetrization triangle on the bespoke powerset model: applied at the dual image Z=⟨M·,x,y⟩ it supplies the Lemma-1 step of the de la Peña forward decoupling bound on the powerset measure.
-- source:
--   de la Peña, V.H. and Montgomery-Smith, S.J. (1995), Decoupling Inequalities for the Tail Probabilities of Multivariate U-statistics, Ann. Probab. 23 (2), 806-816 (arXiv:math/9309211), Lemma 1 (p.2, lines 127-140 of the arXiv text): P(‖X‖≥t) ≤ 3 P(‖X+Y‖≥ 2t/3) for i.i.d. X,Y.

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_bernoulli_measure
open MatrixCompletion
open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory

theorem dlp_bernoulli_three_copy_triangle_scalar
    {n1 n2 : Nat} (p : NNReal) (hp : p ≤ 1)
    (Z : Finset (Fin n1 × Fin n2) → ℝ) (t : ℝ) :
    bernoulliEventProb (p : ℝ) (fun Omega => t ≤ |Z Omega|)
      ≤ 3 * bernoulliTripleEventProb (p : ℝ)
              (fun Omega1 Omega2 _Omega3 => 2 * t / 3 ≤ |Z Omega1 + Z Omega2|) := by
  sorry
