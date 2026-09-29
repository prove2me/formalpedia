-- Prove2me | Theorems.Thm_rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity
-- name    : rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T17:50:26.665215+00:00
-- url     : https://prove2.me/theorems/fe80cd12-12f4-45ce-b240-ec049b8838a1
-- title:
--   Bonami's lemma for trilinear Rademacher chaos ($L^4$–$L^2$)
-- statement:
--   **Degree-3 (trilinear) Rademacher-chaos $L^4\leftrightarrow L^2$ hypercontractivity (Bonami's Lemma, $d=3$).** For a purely-trilinear, off-diagonal (tetrahedral) Rademacher chaos in independent symmetric signs $\varepsilon_w\in\{\pm1\}$, $\xi(\varepsilon)=\sum_{w_1,w_2,w_3\ \text{distinct}} a_{w_1w_2w_3}\,\varepsilon_{w_1}\varepsilon_{w_2}\varepsilon_{w_3}$, the fourth moment is dimension-free controlled by the square of the second moment: $$\mathbb{E}[\xi^4]\le 729\,(\mathbb{E}[\xi^2])^2,$$ i.e. $\|\xi\|_4\le 3\,\|\xi\|_2$ wait — the $(\sqrt3)^d$ Bonami constant at $d=3$, in fourth-moment form $3^{2\cdot3}=9^3=729$. The signs are the symmetric ($p=1/2$) Rademacher variables under the uniform expectation `rademacherExpectation`; `rademacherSign eps i j` is $+1$ if $(i,j)\in eps$ else $-1$; the tetrahedral guard `w1=w2 ∨ w1=w3 ∨ w2=w3` zeroes the diagonal so $\xi$ is genuinely degree-3. This is the order-3 analogue of the degree-2 node `rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity` (constant $81=9^2$) and the $\sigma$-randomized degree-3 chaos hypercontractivity that de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 2 uses for the **order-3 U-statistic** (their eq (23) $\sigma$-randomization produces a multilinear sign chaos of degree $\le 3$). **Source:** R. O'Donnell, *Analysis of Boolean Functions*, §9.1, Bonami's Lemma — a degree-$\le k$ multilinear polynomial of i.i.d. Rademachers is $9^k$-reasonable, $\mathbb{E}[f^4]\le 9^k(\mathbb{E}[f^2])^2$; proved by induction on the number of coordinates with a single-coordinate two-point base case, so it holds for every fixed degree $k$ ($k=2\Rightarrow81$, $k=3\Rightarrow729$). Equivalently A. Bonami 1970 (Ann. Inst. Fourier 20).
-- source:
--   O'Donnell, Analysis of Boolean Functions, §9.1 (Bonami's Lemma); A. Bonami 1970, Ann. Inst. Fourier 20; de la Peña–Montgomery-Smith 1995, arXiv:math/9309211, §4 Lemma 2 (order-3 U-statistic).

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion
open scoped BigOperators Classical

theorem rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity
    {n₁ n₂ : ℕ}
    (a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation (n1 := n₁) (n2 := n₂)
        (fun eps =>
          (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂, ∑ w3 : Fin n₁ × Fin n₂,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
             else a w1 w2 w3 * rademacherSign eps w1.1 w1.2
                            * rademacherSign eps w2.1 w2.2
                            * rademacherSign eps w3.1 w3.2)) ^ 4) ≤
      729 * (rademacherExpectation (n1 := n₁) (n2 := n₂)
              (fun eps =>
                (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂, ∑ w3 : Fin n₁ × Fin n₂,
                  (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                   else a w1 w2 w3 * rademacherSign eps w1.1 w1.2
                                  * rademacherSign eps w2.1 w2.2
                                  * rademacherSign eps w3.1 w3.2)) ^ 2)) ^ 2 := by sorry
