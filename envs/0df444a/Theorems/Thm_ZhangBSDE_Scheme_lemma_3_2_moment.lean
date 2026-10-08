-- Prove2me | Theorems.Thm_ZhangBSDE_Scheme_lemma_3_2_moment
-- name    : ZhangBSDE.Scheme.lemma_3_2_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:07.474813+00:00
-- url     : https://prove2.me/theorems/45a430b4-29bd-4e55-8f01-f417b5e7b14b
-- title:
--   Lemma 3.2 (3.1), p. 465 — ‖Z_t‖_p ≤ C_p(1+|x|) for a.e. t
-- statement:
--   Assume Assumption 2.3 with constant $K$, and let $(X,Y,Z)$ solve the forward–backward SDE (2.1) started at $x\in\mathbb R^d$. For every $p\ge2$ there is a constant $C_p>0$, depending only on $T$, $K$, $p$ (and the dimension $d$), such that
--   $$\|Z_t\|_p\le C_p(1+|x|)\qquad\text{for a.e. } t\in[0,T],$$
--   where $\|\cdot\|_p$ is the $L^p(P)$ norm.
--
--   This moment bound on the martingale integrand is used in the proof of the $L^2$-regularity theorem (Theorem 3.1) to obtain uniform integrability of $\{Z_t\}$.
--
--   **Formalization Note** $C_p$ is chosen before the probability space, the data and the solution, so it is uniform over them. The dependence on $d$ is implicit in the paper, which fixes $d$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, Lemma 3.2 (3.1), p. 465

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

namespace ZhangBSDE.Scheme

/-- Lemma 3.2, (3.1) (p. 465): under Assumption 2.3, for every `p ≥ 2` there is `C_p > 0`,
depending only on `T`, `K`, `p` (and `d`), with `‖Z_t‖_p ≤ C_p (1 + |x|)` for a.e. `t ∈ [0, T]`. -/
theorem lemma_3_2_moment {d : ℕ} (T : ℝ≥0) (K p : ℝ) (hT : 0 < T) (hK : 0 < K) (hp : 2 ≤ p) :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin 1 → ℝ) (hB : IsStdBrownian P B)
        (x : EuclideanSpace ℝ (Fin d)) (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
        (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ),
        Assumption23 T K b σ f Φ →
        ∀ (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y Z : ℝ≥0 → Ω → ℝ),
        IsFBSDESolution (augmentedFiltration P hB) P T (fun t ω => B t ω 0) x b σ f Φ X Y Z →
        ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
          eLpNorm (Z t.toNNReal) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * (1 + ‖x‖)) := by sorry

end ZhangBSDE.Scheme
