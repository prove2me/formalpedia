-- Prove2me | Theorems.Thm_rademacher_mixed3_chaos_l4_l2_bonami_hypercontractivity
-- name    : rademacher_mixed3_chaos_l4_l2_bonami_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-24T02:38:21.728302+00:00
-- url     : https://prove2.me/theorems/8cefe732-003b-4842-a95d-6fdf195ccb79
-- statement:
--   Degree-≤3 mixed (linear + bilinear + trilinear) Rademacher-chaos L4-L2 hypercontractivity (Bonami's lemma at degree 3): for any linear coefficients b, off-diagonal bilinear coefficients a, and all-distinct trilinear coefficients c, the mixed sign-chaos xi(eps) = sum_w b_w*eps_w + sum_{w1!=w2} a*eps*eps + sum_{w1,w2,w3 all distinct} c*eps*eps*eps satisfies E[xi^4] <= 729*(E[xi^2])^2. Source: O'Donnell, Analysis of Boolean Functions, sec 9.1 (degree-<=k multilinear Rademacher polynomial is 9^k-reasonable); Bonami 1970; de la Pena-Montgomery-Smith 1995 (arXiv:math/9309211) sec 4 Lemma 2 via Kwapien-Szulga 1991 eq 1.4. 9^3=729.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped BigOperators Classical

theorem rademacher_mixed3_chaos_l4_l2_bonami_hypercontractivity
    {n₁ n₂ : ℕ}
    (b : (Fin n₁ × Fin n₂) → ℝ)
    (a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ)
    (c : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation (n1 := n₁) (n2 := n₂)
        (fun eps =>
          ((∑ w : Fin n₁ × Fin n₂, b w * rademacherSign eps w.1 w.2)
            + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                (if w1 = w2 then (0 : ℝ)
                 else a w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2))
            + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂, ∑ w3 : Fin n₁ × Fin n₂,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                 else c w1 w2 w3 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2
                              * rademacherSign eps w3.1 w3.2))) ^ 4) ≤
      729 * (rademacherExpectation (n1 := n₁) (n2 := n₂)
              (fun eps =>
                ((∑ w : Fin n₁ × Fin n₂, b w * rademacherSign eps w.1 w.2)
                  + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                      (if w1 = w2 then (0 : ℝ)
                       else a w1 w2 * rademacherSign eps w1.1 w1.2
                                    * rademacherSign eps w2.1 w2.2))
                  + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂, ∑ w3 : Fin n₁ × Fin n₂,
                      (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                       else c w1 w2 w3 * rademacherSign eps w1.1 w1.2
                                    * rademacherSign eps w2.1 w2.2
                                    * rademacherSign eps w3.1 w3.2))) ^ 2)) ^ 2 := by
  sorry
