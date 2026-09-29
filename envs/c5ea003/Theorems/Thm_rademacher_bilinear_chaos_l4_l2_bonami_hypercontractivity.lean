-- Prove2me | Theorems.Thm_rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity
-- name    : rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T02:01:11.471459+00:00
-- url     : https://prove2.me/theorems/ddd7e198-5b29-4fbb-8283-d32bd6fc0106
-- statement:
--   **Degree-2 (bilinear) Rademacher-chaos $L^4\leftrightarrow L^2$ hypercontractivity (Bonami's lemma, $d=2$).** For a purely-bilinear, off-diagonal (tetrahedral) Rademacher chaos in independent symmetric signs $\varepsilon_w \in \{\pm 1\}$, $\ \xi(\varepsilon) = \sum_{w_1 \neq w_2} a_{w_1 w_2}\,\varepsilon_{w_1}\varepsilon_{w_2}$, the fourth moment is dimension-free controlled by the square of the second moment: $$\mathbb{E}[\xi^4] \le 81\,(\mathbb{E}[\xi^2])^2,$$ i.e. $\|\xi\|_4 \le 3\|\xi\|_2$ (the $(\sqrt3)^d$ Bonami constant at $d=2$, in fourth-moment form $3^4=81$). The signs are the symmetric ($p=1/2$) Rademacher variables under the uniform expectation `rademacherExpectation`. This is the $\sigma$-randomized degree-2 chaos hypercontractivity that de la Peña–Montgomery-Smith 1995 Lemma 2 invokes ("since the $\epsilon$'s are hypercontractive, by equation (1.4) of Kwapień and Szulga (1991)"), supplying the constant $K$ to the assembled Lemma-2 lower bound. Its proof is the Bonami two-point inequality (the $n=1$ base case) tensorized over the discrete cube and projected to degree 2 — genuinely Mathlib-absent infrastructure (rev c5ea003 has zero hypercontractivity / zero Bonami two-point inequality / zero Rademacher-chaos moment comparison). The true sup of $\mathbb{E}[\xi^4]/(\mathbb{E}[\xi^2])^2$ is $\approx 5.4$ (numerically verified), well within 81.
-- source:
--   A. Bonami, Ann. Inst. Fourier 20 (1970) 335–402 (the (4,2)-hypercontractive / two-point inequality); Kwapień–Szulga, Ann. Probab. 19 (1991) 369–379, eq. 1.4; de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), Lemma 2.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped BigOperators Classical

theorem rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity
    {n₁ n₂ : ℕ} (a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation (n1 := n₁) (n2 := n₂)
        (fun eps =>
          (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
            (if w1 = w2 then (0 : ℝ)
             else a w1 w2 * rademacherSign eps w1.1 w1.2
                          * rademacherSign eps w2.1 w2.2)) ^ 4) ≤
      81 * (rademacherExpectation (n1 := n₁) (n2 := n₂)
              (fun eps =>
                (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  (if w1 = w2 then (0 : ℝ)
                   else a w1 w2 * rademacherSign eps w1.1 w1.2
                                * rademacherSign eps w2.1 w2.2)) ^ 2)) ^ 2 := by sorry
