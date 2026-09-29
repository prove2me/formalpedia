-- Prove2me | Theorems.Thm_allikvere_lemma63_eventually
-- name    : allikvere_lemma63_eventually
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T10:54:20.18514+00:00
-- url     : https://prove2.me/theorems/e0ada8f7-b4dc-4c94-ba60-03f8502ae2cf
-- title:
--   Residue equidistribution of a first-passage stopping set (Allikvere Lemma 6.3)
-- statement:
--   Fix $\alpha=1.001$. For $x\in\mathbb{R}$ with $x>1$, set $$m_0=\left\lfloor\frac{\log x}{100000}\right\rfloor$$ and define $$R_x=\left[ e^{-(\log x)^{7/10}}\left(\frac{4}{3}\right)^{m_0}x,\ e^{(\log x)^{7/10}}\left(\frac{4}{3}\right)^{m_0}x\right].$$ Let $$E'(x)=\left\{M\in\mathbb{N}: M\text{ is positive and odd},\ M\in R_x,\ x<\operatorname{Syracuse}^j(M)\text{ for every }j<m_0,\ 1\le\operatorname{Syracuse}^{m_0}(M)\le x\right\}.$$ There exists $x_0\in\mathbb{R}$ with $x_0>1$ such that, for every $x\in\mathbb{R}$ with $x_0\le x$, every order-connected $W\subseteq\mathbb{R}$, every $k\in\mathbb{N}$, and every residue $r\in\mathbb{Z}/3^k\mathbb{Z}$, the bound is $$\left|\#\{M\in E'(x): (M: \mathbb{R})\in W,\ M\equiv r\pmod{3^k}\} - 3^{-k}\#\{M\in E'(x): (M: \mathbb{R})\in W\}\right|\le x^{1/10000}.$$ Its role is to provide the residue-class counting input for the density argument in Allikvere Lemma 6.3. This is not Tao Corollary 6.3.
-- source:
--   Jaan Allikvere, "Almost all Collatz orbits attain almost bounded values in natural density", Zenodo record 21499244, July 2026, version 2, author/title lines 32-33 and Lemma 6.3 lines 1126-1208 in local allikvere-2026-07-natural-density-v2.tex. Tao's (5.10) range is an input to the stopping-set definition; the target is Allikvere's Lemma 6.3, not Tao Corollary 6.3. https://zenodo.org/records/21499244

import Mathlib
import Definitions.Def_allikvere_stopping_set

theorem allikvere_lemma63_eventually :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ W : Set ℝ, W.OrdConnected →
      ∀ k : ℕ, ∀ r : Fin (3 ^ k),
        |((((allikvereEPrime x ∩ allikvereRealPreimage W) ∩
            {M | M % 3 ^ k = r.val}).ncard : ℝ) -
          ((allikvereEPrime x ∩ allikvereRealPreimage W).ncard : ℝ) /
            (3 ^ k : ℝ))| ≤ Real.rpow x (1 / 10000 : ℝ) := by sorry
