-- Prove2me | Theorems.Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr
-- name    : iteratedFDeriv_smul_comp_apply_append_inl_inr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/90c7aea2-3f03-5543-9a77-21bbfbe3f709
-- title:
--   Separated-variables product rule on tangential and normal slots
-- statement:
--   Let $E$ and $F$ be real normed spaces (normed additive commutative groups with real normed space structures), let $\varphi : \mathbb{R} \to \mathbb{R}$ and $A : E \to F$ both be $C^\infty$ over $\mathbb{R}$ (`ContDiff ℝ ⊤`), and consider the map $P : E \times \mathbb{R} \to F$, $P(p) = \varphi(p_2) \cdot A(p_1)$, the scalar action of $\varphi(p_2) \in \mathbb{R}$ on $A(p_1) \in F$. Fix natural numbers $j, l$, a point $e \in E$, a real number $\rho$, and a family $u : \mathrm{Fin}\, j \to E$. Then the $(j+l)$-st iterated Fréchet derivative of $P$ at the point $(e,\rho)$, a continuous multilinear map in $j+l$ arguments from $E \times \mathbb{R}$, evaluated on the concatenated family (`Fin.append`) consisting of the $j$ tangential vectors $(u_i, 0)$ followed by $l$ copies of the normal vector $(0,1)$, equals the scalar $\frac{d^l\varphi}{d\rho^l}(\rho)$ (`iteratedDeriv l φ ρ`) times the value $D^j A(e)(u_1,\dots,u_j)$ of the $j$-th iterated Fréchet derivative of $A$ at $e$ on $u$.
--
--   This is the Leibniz rule for a function of separated-variables product form, in the special case where the evaluation slots are sorted: all tangential directions first, all normal directions last. It is used in the construction of smooth functions with prescribed jets along a hyperplane, namely by [`MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero`](thm.html#MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero) and [`MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero`](thm.html#MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem iteratedFDeriv_smul_comp_apply_append_inl_inr
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
    iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
        (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
      iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u := by sorry
