-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_lemma1
-- name    : ZudilinZeta.zudilin_lemma1
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-22T18:08:38.250001+00:00
-- url     : https://prove2.me/theorems/e912adce-8aab-4800-9b0b-625f335170d1
-- title:
--   Lemma 1: $F_n$ is a $\mathbb{Q}$-linear form in $1, \zeta(r+2), \dots, \zeta(q-2)$, with denominators (3)
-- statement:
--   **Lemma 1 of the note.** The quantity (2) is a linear form in $1, \zeta(r+2), \zeta(r+4), \dots, \zeta(q-2)$ with rational coefficients; moreover the inclusion
--   $$D^r_{m_1 n} D_{m_2 n}\cdots D_{m_{q-r} n}\cdot \Phi_n^{-1}\cdot F_n \in \mathbb{Z} + \mathbb{Z}\zeta(r+2) + \mathbb{Z}\zeta(r+4) + \dots + \mathbb{Z}\zeta(q-2) \tag{3}$$
--   holds.
--
--   The list $\zeta(r+2), \zeta(r+4), \dots, \zeta(q-2)$ is indexed here as $\zeta(r+2k)$ for $k = 1, \dots, (q-r-2)/2$; for the parameters $r = 3$, $q = 13$ of the note this is exactly $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_lemma1 (P : Params) (n : ℕ) (hn : 0 < n) :
    (∃ c : ℕ → ℚ,
        F P n = (c 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (c k : ℝ) * zetaR (P.r + 2 * k)) ∧
      (∃ a : ℕ → ℤ,
        Lambda P n = (a 0 : ℝ)
          + ∑ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), (a k : ℝ) * zetaR (P.r + 2 * k)) := by
  sorry
end ZudilinZeta
