-- Prove2me | Theorems.Thm_rademacher_mixed_chaos_l4_l2_bonami_hypercontractivity
-- name    : rademacher_mixed_chaos_l4_l2_bonami_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T21:50:52.279969+00:00
-- url     : https://prove2.me/theorems/85002e4f-00b6-4dfe-8199-ab0879970037
-- statement:
--   Degree-≤2 MIXED (linear + bilinear) Rademacher-chaos L4-L2 hypercontractivity (Bonami at degree ≤2, constant 9^2=81): for the mixed scalar sign-chaos xi(eps)=sum_w b_w eps_w + sum_{w1≠w2} a_{w1w2} eps_{w1} eps_{w2}, one has E[xi^4] ≤ 81 (E[xi^2])^2. Reference: ODonnell Analysis of Boolean Functions §9.1 (general Bonami lemma); A. Bonami 1970 (Ann. Inst. Fourier 20); used in de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 2 (degree-≤k tetrahedral chaos sum_{r=1}^k) via Kwapień–Szulga 1991 eq. (1.4).
-- source:
--   O Donnell, Analysis of Boolean Functions, §9.1 (general Bonami lemma); A. Bonami 1970 (Ann. Inst. Fourier 20); de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 2; Kwapień–Szulga 1991 eq. (1.4)

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped BigOperators Classical

theorem rademacher_mixed_chaos_l4_l2_bonami_hypercontractivity
    {n₁ n₂ : ℕ}
    (b : (Fin n₁ × Fin n₂) → ℝ)
    (a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation (n1 := n₁) (n2 := n₂)
        (fun eps =>
          ((∑ w : Fin n₁ × Fin n₂, b w * rademacherSign eps w.1 w.2)
            + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                (if w1 = w2 then (0 : ℝ)
                 else a w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2))) ^ 4) ≤
      81 * (rademacherExpectation (n1 := n₁) (n2 := n₂)
              (fun eps =>
                ((∑ w : Fin n₁ × Fin n₂, b w * rademacherSign eps w.1 w.2)
                  + (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                      (if w1 = w2 then (0 : ℝ)
                       else a w1 w2 * rademacherSign eps w1.1 w1.2
                                    * rademacherSign eps w2.1 w2.2))) ^ 2)) ^ 2 := by sorry
