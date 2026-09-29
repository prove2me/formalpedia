-- Prove2me | Theorems.Thm_exists_det_of_apply_ne_zero_of_linearIndependent
-- name    : exists_det_of_apply_ne_zero_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f1c490a1-1b42-57da-a77a-e849f80a11ac
-- title:
--   Unisolvent points exist for a linearly independent family
-- statement:
--   Let $\Bbbk$ be a field, $X$ an arbitrary type, and $\iota$ a finite type with decidable equality. Let $f : \iota \to X \to \Bbbk$ be a family of $\Bbbk$-valued functions on $X$, indexed by $\iota$, and assume that $f$ is linearly independent over $\Bbbk$ in the $\Bbbk$-vector space $X \to \Bbbk$ of all functions (with pointwise operations). The conclusion is that there exists a family of points $x : \iota \to X$, indexed by the same type $\iota$, such that the square $\iota \times \iota$ evaluation matrix whose $(i,j)$ entry is $f_j(x_i)$ has non-zero determinant, i.e. $\det\bigl(f_j(x_i)\bigr)_{i,j \in \iota} \neq 0$. No hypothesis is placed on $X$ beyond its being a type; in particular $X$ may be infinite, and no regularity or topology is involved.
--
--   This is the standard unisolvence statement: a finite linearly independent family of $\Bbbk$-valued functions admits interpolation points at which the evaluation matrix is invertible, equivalently the evaluation functionals at those points form a basis of the dual of the span. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, via [`LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots`](thm.html#LanglandsTunnell.RankinSelberg.exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots), to select finitely many test points at which a family of independent test data can be separated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_det_of_apply_ne_zero_of_linearIndependent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_det_of_apply_ne_zero_of_linearIndependent
    {𝕜 : Type*} [Field 𝕜] {X : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → X → 𝕜) (hf : LinearIndependent 𝕜 f) :
    ∃ x : ι → X, (Matrix.of fun i j : ι => f j (x i)).det ≠ 0 := by sorry
