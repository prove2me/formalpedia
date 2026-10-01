-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_lcm_asymptotics
-- name    : ZudilinZeta.zudilin_lcm_asymptotics
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:22:31.699582+00:00
-- url     : https://prove2.me/theorems/184bd709-31c9-4dee-9979-715c43c00a36
-- title:
--   $\log D_{m_j n} / n \to m_j$ (prime number theorem)
-- statement:
--   The note records that, by the prime number theorem,
--   $$\lim_{n \to \infty} \frac{\log D_{m_j n}}{n} = m_j, \qquad j = 1, \dots, q-r,$$
--   where $D_N = \operatorname{lcm}(1, 2, \dots, N)$.
--
--   This is the asymptotics of the denominator in (3); together with the growth rate of $|F_n|$ from Lemma 2 it produces the comparison $C_0 > C_1$ of Lemma 3.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_lcm_asymptotics (P : Params) (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ P.q - P.r) :
    Filter.Tendsto (fun n : ℕ => Real.log (D (m P j * n) : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (m P j : ℝ)) := by sorry
end ZudilinZeta
