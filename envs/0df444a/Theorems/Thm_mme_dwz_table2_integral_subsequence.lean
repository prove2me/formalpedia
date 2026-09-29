-- Prove2me | Theorems.Thm_mme_dwz_table2_integral_subsequence
-- name    : mme_dwz_table2_integral_subsequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:20:10.640396+00:00
-- url     : https://prove2.me/theorems/121e7c3c-e07f-425e-83ee-f6fe66a37db5
-- title:
--   DWZ Table 2: exact component and restricted-split type subsequence
-- statement:
--   Let $\alpha_s$ be the exact weight of component $s$ in Table 2, and let $z_s(r)$ be its prescribed Section 6.3 Z-split weight. For every natural lower bound $N_0$, there is a tensor power $N>N_0$ and natural-number counts $c_s,d_{s,r}$ such that, for every component $s$ and split index $r$,
--
--   $$
--   N\alpha_s=c_s,\qquad N\alpha_s z_s(r)=d_{s,r}.
--   $$
--
--   Thus the fixed rational Table 2 witness occurs along an unbounded sequence of powers for which all displayed component and restricted-split type classes have exact integral cardinalities. This statement does not cover separately optimized joint split distributions.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023: Definition 3.5 and footnote 10 (PDF p. 23 / printed p. 22), Definition 3.7 (PDF p. 24 / printed p. 23), and the Section 6.3 split specializations and Table 2 (PDF pp. 59-60 / printed pp. 58-59).

import Definitions.Def_mme_dwz_square_data
open MME.DWZSquare

theorem mme_dwz_table2_integral_subsequence (N₀ : ℕ) :
    ∃ N : ℕ, N₀ < N ∧
      (∀ s : Fin 15, ∃ componentCount : ℕ,
        (N : ℝ) * alpha s = componentCount) ∧
      (∀ s : Fin 15, ∀ r : Fin 3, ∃ splitCount : ℕ,
        (N : ℝ) * alpha s * zSplit s r = splitCount) := by sorry
