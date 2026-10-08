-- Prove2me | Theorems.Thm_WorstCaseCVaR_Mixture_lemma_1
-- name    : WorstCaseCVaR.Mixture.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:06.549982+00:00
-- url     : https://prove2.me/theorems/7530c615-cfea-486b-8fa5-f92e3b9b87e2
-- title:
--   Lemma 1 — minimax equality on compact convex sets (with semicontinuity)
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ and $\mathcal Y\subseteq\mathbb R^m$ be nonempty compact convex sets and let $\phi:\mathbb R^n\times\mathbb R^m\to\mathbb R$ be such that $\phi(\cdot,y)$ is convex and lower semicontinuous on $\mathcal X$ for every $y\in\mathcal Y$, and $\phi(x,\cdot)$ is concave and upper semicontinuous on $\mathcal Y$ for every $x\in\mathcal X$. Then there are $x_0\in\mathcal X$ and $y_0\in\mathcal Y$ with
--   $$\min_{x\in\mathcal X}\max_{y\in\mathcal Y}\phi(x,y)=\phi(x_0,y_0)=\max_{y\in\mathcal Y}\min_{x\in\mathcal X}\phi(x,y),$$
--   the outer minimum attained at $x_0$ and the outer maximum at $y_0$.
--
--   This minimax theorem (Fan 1953) is the tool that exchanges the minimization over $\alpha$ and the maximization over the weights $\lambda$.
--
--   **Formalization Note** The paper's statement has no continuity hypothesis; without one the minimum and maximum need not exist (on $[0,1]^2$, $\phi(x,y)=x$ for $x>0$ and $\phi(0,y)=1$). The two semicontinuity hypotheses are those of Fan's theorem and are added. The inner $\max_y$ and $\min_x$ are the real `sSup`/`sInf`, attained by semicontinuity on compact sets.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1157, Lemma 1 (citing Fan 1953)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Mixture_Setting

open MeasureTheory

namespace WorstCaseCVaR.Mixture

theorem lemma_1 {m n : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y,
      IsLeast ((fun x => sSup ((fun y => φ x y) '' Y)) '' X) (φ x₀ y₀) ∧
        IsGreatest ((fun y => sInf ((fun x => φ x y) '' X)) '' Y) (φ x₀ y₀) := by sorry

end WorstCaseCVaR.Mixture
