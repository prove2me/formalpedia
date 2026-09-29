-- Prove2me | Theorems.Thm_dlp_four_corner_sigma_average_eq_copy_sum_k2_inl
-- name    : dlp_four_corner_sigma_average_eq_copy_sum_k2_inl
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:32:16.003162+00:00
-- url     : https://prove2.me/theorems/c7b93821-7da1-4ab6-b9f5-f2bb5181a1f1
-- statement:
--   **Concrete $T_{n,2}$ σ-average identity** (de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4). At the two distinct indices $i_1\neq i_2$ the σ-block is the four sign configurations $(\sigma_1,\sigma_2)\in\{\pm1\}^2$, each with uniform weight $\tfrac14$; here the sign at a slot is read off `Fin 2` by $b\mapsto(\text{if }b=0\text{ then }+1\text{ else }-1)$. Averaging the eq-(4) four-corner σ-randomized term $4\,f(Z^{(l_1)},Z^{(l_2)})$ over this block recovers the plain four-corner copy-sum $\sum_{j_1,j_2} f(X^{(j_1)},X^{(j_2)})$ — the inner summand of $T_{n,2}$. This is the pointwise (per index pair) form of $T_{n,2}=2^2\sum_{i_1\neq i_2}\mathbb E(f(Z^{(l_1)},Z^{(l_2)})\mid G_2)$: the σ-cross-terms cancel because each $\sigma$ is symmetric mean-zero, so the uniform σ-average of the four sign products $(1+s_1\sigma_1)(1+s_2\sigma_2)$ equals $1$. Combined with the σ-conditional-expectation substrate (dlp_sigma_randomization_condexp_eq_sigma_integral), which identifies $\mathbb E(g(\sigma)\mid G_2)$ with the σ-average $\int g\,d\nu$, this yields the conditional-expectation form of $T_{n,2}$. (`dlpCopyPerm σ` is the σ-permutation of the two i.i.d. copies from the imported `dlp_sigma_randomization` definition.)
-- source:
--   de la Peña & Montgomery-Smith, Decoupling inequalities for the tail probabilities of multivariate U-statistics, Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4 (construction of T_{n,2}, eq (4)).

import Definitions.Def_dlp_sigma_randomization
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Fin

open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_four_corner_sigma_average_eq_copy_sum_k2_inl
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → V) :
    (1 / 4 : ℝ) • ∑ b₁ : Fin 2, ∑ b₂ : Fin 2,
        (4 : ℝ) • f
          (dlpCopyPerm (if b₁ = 0 then (1 : ℝ) else -1) l₁)
          (dlpCopyPerm (if b₂ = 0 then (1 : ℝ) else -1) l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, f j₁ j₂ := by sorry
