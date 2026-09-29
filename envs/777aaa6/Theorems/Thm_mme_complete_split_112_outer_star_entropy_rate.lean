-- Prove2me | Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
-- name    : mme_complete_split_112_outer_star_entropy_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:47:09.319195+00:00
-- url     : https://prove2.me/theorems/2228586e-7079-407b-a129-63045f04300f
-- title:
--   Exact-profile outer-star counts attain the ternary entropy rate
-- statement:
--   Let $l,g$ be nonnegative integers with $D=l+g>0$, and put $p=l/(2D)$. Let $C$ be any real constant and $\delta>0$. For every sufficiently large natural $m$, put $N=Dm$ and
--
--   $$Z_m=\binom{2N}{lm}\binom{2N-lm}{lm}.$$
--
--   Every positive real $a$ satisfying $Z_m e^{-C\sqrt{N+1}}\le a$ then satisfies
--
--   $$2N\bigl(H(p,p,1-2p)-\delta\bigr)\le\log a.$$
--
--   All logarithms and the entropy $H(x_1,x_2,x_3)=-\sum_i x_i\log x_i$ use natural units, with zero-mass terms interpreted as zero. Individual cells may vanish. The threshold depends on $l,g,C,\delta$, not on $a$.
--
--   This turns the actual uniform-star lower bound into the source's outer-direction entropy rate along exactly compatible lengths. It assumes neither an entropy asymptotic nor any tensor-value or matrix-multiplication-exponent bound. The Lean statement represents natural entropy as $\log 2$ times the existing entropy-in-bits definition.
-- source:
--   Finite-to-rate adapter for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15), with the112 directional term given explicitly in the pinned OSF release https://osf.io/mw5ak/, src/evaluation/TermInfoLv2.m lines134–146, especially line135. The exact first released profile uses l=8959763742786037, g=1180582660953668517387, D=1180591620717411303424 and params(923) in data/W1.00_2.371339.mat (SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3). Reuses the zero-cell-safe proved multinomial polynomial lower theorem mme_dwz_multinomial_entropy_polynomial_lower, ID2e42e907-1a53-420b-910e-0dae2ae915a9, and the independent logarithmic/square-root loss absorption theorem. The explicit finite polynomial estimate is an implementation lemma, not claimed to be a separately numbered theorem in the modern paper.

import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.VecNotation

open Filter

set_option autoImplicit false

theorem mme_complete_split_112_outer_star_entropy_rate
    (l g : ℕ) (hD : 0 < l + g) (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N : ℕ := (l + g) * m
      let p : ℝ := (l : ℝ) / (2 * ((l + g : ℕ) : ℝ))
      ∀ a : ℝ, 0 < a →
        (((Nat.choose (2 * N) (l * m) *
          Nat.choose (2 * N - l * m) (l * m) : ℕ) : ℝ) *
            Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ a) →
        (2 * N : ℕ) *
          (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log a := by sorry
