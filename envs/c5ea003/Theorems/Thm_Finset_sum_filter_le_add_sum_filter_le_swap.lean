-- Prove2me | Theorems.Thm_Finset_sum_filter_le_add_sum_filter_le_swap
-- name    : Finset.sum_filter_le_add_sum_filter_le_swap
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T19:05:25.416968+00:00
-- url     : https://prove2.me/theorems/c2d8e124-e804-4461-adcf-731edcdedb61
-- title:
--   Triangular rearrangement of a double sum
-- statement:
--   Let $\iota$ be a linearly ordered type and $M$ an additive commutative monoid. Let $s$ be a finite set of indices and $f:\iota\times\iota\to M$ a kernel vanishing on the diagonal, $f(x,x)=0$ for all $x$. Write $s_{\le t}=\{u\in s:u\le t\}$ for the closed lower slice. Then\n\n$$\sum_{t\in s}\sum_{u\in s_{\le t}}f(u,t)+\sum_{t\in s}\sum_{u\in s_{\le t}}f(t,u)=\sum_{x\in s}\sum_{y\in s}f(x,y).$$\n\nThe left side adds the lower-triangular sum and its transpose; they overlap exactly on the diagonal where the kernel vanishes, recovering the full double sum. This is the `Finset` analogue of triangular rearrangements used in polygon area estimates.\n\n**Formalization Note** Lean states the slices with `Finset.filter`; no integrability or finiteness beyond `Finset` is needed.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Algebra/BigOperators/Triangle.lean#L22-L26

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
open Finset

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]

theorem sum_filter_le_add_sum_filter_le_swap (s : Finset ι) (f : ι → ι → M) (hdiag : ∀ x, f x x = 0) : ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) + ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u) = ∑ x ∈ s, ∑ y ∈ s, f x y := by sorry

end Finset
