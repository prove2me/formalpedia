-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoffInverse_le_explicit
-- name    : BanditAlgorithm.chernoffInverse_le_explicit
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:56:51.073604+00:00
-- url     : https://prove2.me/theorems/2348b8bb-7435-4636-8dd7-ffa5e2a76ce9
-- title:
--   Explicit O(k + log(1/δ)) bound on the Chernoff inverse
-- statement:
--   An explicit upper bound on the threshold constant of Lattimore--Szepesv\'ari Lemma 33.7: for $k\ge1$ and $\delta\in(0,1]$,
--   $$f^{-1}(\delta)\le\frac{k+\log(1/\delta)}{1-e^{-1}},$$
--   where $f(x)=e^{k-x}(x/k)^k$.
--
--   Lemma 33.7 supplies $f^{-1}(\delta)$ only implicitly, but the sample-complexity half of Theorem 33.6 needs it to grow like $\log(1/\delta)$ and no faster. The proof bounds $\log f(x)=k-x+k\log(x/k)$ using $\log u\le u-1$ in the form $k\log(x/k)\le e^{-1}x + k\log k - k$ -- a linear majorant with slope $e^{-1}<1$ -- so that $\log f(x)\le -(1-e^{-1})x+k$.
-- source:
--   Explicit upper bound on the threshold constant f^{-1}(delta) of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. The O(log(1/delta)) growth is used in the sample-complexity half of Theorem 33.6, not in Lemma 33.7 itself.

import Definitions.Def_TrackAndStop

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

theorem BanditAlgorithm.chernoffInverse_le_explicit {k : ℕ} (hk : 0 < k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    BanditAlgorithm.chernoffInverse k δ
      ≤ ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  sorry
