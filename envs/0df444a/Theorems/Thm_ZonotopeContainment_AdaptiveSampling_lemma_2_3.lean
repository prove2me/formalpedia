-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_3
-- name    : ZonotopeContainment.AdaptiveSampling.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:16.311508+00:00
-- url     : https://prove2.me/theorems/fb786609-5865-462f-b761-3e4363e58b13
-- title:
--   Lemma 2.3 — Lewis and support bounds
-- statement:
--   Let $d\ge3$, $C\ge64$, and start Algorithm 1 from generators $w$ and an approximate Lewis map $T$. For every draw sequence, every state $0\le j\le R$, and every functional $b\in\mathbb R^d$,
--   $$L(v_j)\preceq I,\qquad h_{Z(v_j)}(b)\le\sqrt d\,\|b\|.$$
--   Initially the reverse estimate is
--   $$h_{Z(v_0)}(b)\ge\frac{\|b\|}{4}\quad\text{for every }b\in\mathbb R^d.$$
--   These three bounds control the support of the evolving zonotope throughout a complete run, including its terminal state.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators have zero projection and matrix contribution, weight one, and stay zero; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: the computational input model uses rational generator matrices → arbitrary real generator families; reason: the geometric and Gaussian statements apply to these families and specialize to rational input
--   - generalization: a fixed absolute algorithm constant C ≥ 64 → every C ≥ 64, with existential constants chosen after C where needed; reason: the analysis fixes C first and chooses the remaining constants afterwards, uniformly in all other data
--   - encoding: the initial transformed functional b₀ → every initial functional b; reason: the initial map is invertible, so its transpose ranges over all functionals
--   - generalization: T is computed once in a preprocessing step, by approximating Lewis weights (p. 5) → any invertible matrix T with ¼I ⪯ L(Tw) ⪯ I, taken as an input (ApproxLewis w T); its computation is not formalized; reason: Algorithm 1 uses T only through these properties, so the statement covers every map the preprocessing can return
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Lemma 2.3, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- Lemma 2.3, p. 7, including the initial lower support bound. -/
theorem lemma_2_3 (d n : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) (z : Tape d) :
    (∀ j ≤ rounds d,
      lewis (runState C w T z j).v ≤ (1 : Mat d) ∧
      ∀ b : E d, support (runState C w T z j).v b ≤ Real.sqrt d * ‖b‖) ∧
    (∀ b : E d, ‖b‖ / 4 ≤ support (runState C w T z 0).v b) := by sorry

end ZonotopeContainment.AdaptiveSampling
