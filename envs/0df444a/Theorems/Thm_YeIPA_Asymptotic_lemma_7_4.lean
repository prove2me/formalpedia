-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_lemma_7_4
-- name    : YeIPA.Asymptotic.lemma_7_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:25.383153+00:00
-- url     : https://prove2.me/theorems/63cd9d7f-ba61-4f4d-856f-094f3bc4b53c
-- title:
--   Lemma 7.4 — (d_x)_P and d_y solve weighted least-squares problems on the optimal partition
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$, let $(x,y,s)$ be an interior point ($Ax=b$, $x>0$, $A^Ty+s=c$, $s>0$), let $(P,Z)=(P^*,Z^*)$ be the strict complementarity partition, $D=X^{1/2}S^{-1/2}$ with entries $D_j=\sqrt{x_j/s_j}$, and let $(d_x,d_y,d_s)$ solve the predictor system (7.4). Write $A_P$, $A_Z$ for the columns of $A$ indexed by $P$, $Z$. Then:
--
--   1. $(d_x)_P$ is the (unique) solution of the weighted least-squares problem
--   $$\min_u\ \tfrac12\|D_P^{-1}u\|^2\quad\text{s.t.}\quad A_Pu=-A_Z(d_x)_Z ;$$
--   2. $d_y$ is a solution of the weighted least-squares problem
--   $$\min_v\ \tfrac12\|D_ZA_Z^Tv\|^2\quad\text{s.t.}\quad A_P^Tv=-(d_s)_P ,$$
--   and every solution $v$ of it satisfies $(d_s)_Z=-A_Z^Tv$.
--
--   The lemma identifies the parts of the predictor direction on the "large" indices ($P$ for $d_x$, $Z$ for $d_s$) as solutions of least-squares problems whose data are the small parts estimated in Lemma 7.3; this is what makes those parts $O(\mu)$ in Theorem 7.5.
--
--   **Formalization Note** Part 2 corrects two misprints of p. 215, recorded as finding F1: the page writes the objective $\tfrac12\|D_Zv\|^2$, which is not defined for $v\in\mathbb R^m$ (the KKT check in the proof on p. 216 is for $\tfrac12\|D_ZA_Z^Tv\|^2$), and writes $(d_s)_Z=A_Z^Tv$, whereas (7.4) gives $(d_s)_Z=-A_Z^Td_y$ for the $v=d_y$ the proof exhibits, which satisfies the printed constraint $A_P^Tv=-(d_s)_P$. Vectors $u$ of part 1 are full vectors in $\mathbb R^n$ vanishing off $P$, so $A_Pu$ is $Au$; uniqueness is stated as strict inequality of the objective against every other feasible $u$. Part 2 has no unique minimizer in $v$ in general; what is unique is $A_Z^Tv$, which is what "every solution $v$ gives $(d_s)_Z=-A_Z^Tv$" states. The objective norms are Euclidean. The rank condition on $A$ is the book's standing assumption; the interior point is the book's standing $(x,s)$ (p. 214).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 215–216, Lemma 7.4

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_LP

open Matrix

namespace YeIPA.Asymptotic

/-- Lemma 7.4 (pp. 215–216). Let `(x, y, s)` be an interior feasible point, `rank A = m`,
`(P, Z) = (P*, Z*)`, `Dⱼ = √(xⱼ/sⱼ)`, and let `(d_x, d_y, d_s)` solve the predictor system
(7.4). Then
1. `(d_x)_P` is the unique solution of the weighted least-squares problem
   `min_u (1/2)‖D_P⁻¹ u‖²` s.t. `A_P u = −A_Z (d_x)_Z` (vectors `u` written as full vectors
   vanishing off `P`, so `A_P u = A u`);
2. `d_y` solves the weighted least-squares problem `min_v (1/2)‖D_Z A_Zᵀ v‖²` s.t.
   `A_Pᵀ v = −(d_s)_P`, and every solution `v` of it gives `(d_s)_Z = −A_Zᵀ v`.
Part 2 is the page's second problem with its misprints corrected (the page prints the
objective `‖D_Z v‖²` and `(d_s)_Z = A_Zᵀ v`; see the natural-language statement). -/
theorem lemma_7_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : A.rank = m) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hint : IsInterior A b c x y s) (hdir : IsPredictorDirection A x s dx dy ds) :
    -- part 1: the feasible set of the first problem, and its objective
    (let U : Set (Fin n → ℝ) := {u | (∀ j, j ∉ Pstar A b c → u j = 0) ∧
          A *ᵥ u = -(A *ᵥ (Zstar A b c).indicator dx)}
     let f : (Fin n → ℝ) → ℝ := fun u => (1 / 2) * ∑ j, (u j / scaling x s j) ^ 2
     (Pstar A b c).indicator dx ∈ U ∧
       ∀ u ∈ U, u ≠ (Pstar A b c).indicator dx → f ((Pstar A b c).indicator dx) < f u) ∧
    -- part 2: the feasible set of the second problem, and its objective
    (let V : Set (Fin m → ℝ) := {v | ∀ j ∈ Pstar A b c, (Aᵀ *ᵥ v) j = -ds j}
     let g : (Fin m → ℝ) → ℝ := fun v =>
       (1 / 2) * ∑ j, ((Zstar A b c).indicator (fun i => scaling x s i * (Aᵀ *ᵥ v) i) j) ^ 2
     dy ∈ V ∧ (∀ v ∈ V, g dy ≤ g v) ∧
       ∀ v ∈ V, g v = g dy → ∀ j ∈ Zstar A b c, ds j = -(Aᵀ *ᵥ v) j) := by sorry

end YeIPA.Asymptotic
