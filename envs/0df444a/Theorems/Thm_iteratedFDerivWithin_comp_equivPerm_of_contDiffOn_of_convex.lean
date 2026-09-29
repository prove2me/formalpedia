-- Prove2me | Theorems.Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
-- name    : iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/4263e16a-859a-5bf0-bb2b-ea22771719b1
-- title:
--   Symmetry of iterated derivatives within a convex set
-- statement:
--   Let $E$ and $F$ be real normed spaces (each a normed additive commutative group with a real normed space structure), and let $s \subseteq E$ be a set that is convex over $\mathbb{R}$ and whose interior is nonempty. Let $n$ be a natural number and $f : E \to F$ a map that is of class $C^n$ on $s$ in the sense of `ContDiffOn ℝ n f s`, and let $x$ be a point of $s$ — no interiority of $x$ is required, so boundary points are allowed. Then for every permutation $\sigma$ of `Fin n` and every family $v : \mathrm{Fin}\,n \to E$ of vectors, the $n$-th iterated derivative of $f$ within $s$ at $x$, the continuous $n$-multilinear map `iteratedFDerivWithin ℝ n f s x`, takes the same value on the permuted family $v \circ \sigma$ as on $v$. Equivalently, $D^n_s f(x)$ is a symmetric $n$-linear map: $D^n_s f(x)(v_{\sigma(0)},\dots,v_{\sigma(n-1)}) = D^n_s f(x)(v_0,\dots,v_{n-1})$.
--
--   This is the Schwarz–Clairaut symmetry of higher derivatives, in the relative form for derivatives taken within a convex set with nonempty interior and at arbitrary points of that set, for all permutations of the arguments rather than just transpositions of adjacent slots. It serves the construction of smooth functions with prescribed jets on half-spaces, being used in [`MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero`](thm.html#MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero) and [`MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero`](thm.html#MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f s) {x : E} (hx : x ∈ s)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v := by sorry
