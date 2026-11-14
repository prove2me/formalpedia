-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_finite_supermodular_telescoping
-- name    : ZeroFreeRRG.Hardcore.finite_supermodular_telescoping
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:07:57.695124+00:00
-- url     : https://prove2.me/theorems/3a4c5b12-c1c1-49f8-9321-65ddf5cb7d04
-- title:
--   Supermodular finite-difference telescoping inequality
-- statement:
--   Let $v$ be a real-valued function of finite sets whose mixed difference is nonnegative whenever two new elements are inserted. For every finite set $S$, $$v(S)\ge v(\varnothing)+\sum_{i\in S}(v(\{i\})-v(\varnothing)).$$ This is the finite telescoping inequality underlying the supermodularity step in the hardcore Bethe monotonicity argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem finite_supermodular_telescoping {ι : Type} [DecidableEq ι] (v : Finset ι → ℝ)
    (hSM : ∀ S : Finset ι, ∀ i j, i ∉ S → j ∉ S → i ≠ j →
      v (insert i (insert j S)) + v S ≥ v (insert i S)+v (insert j S))
    (S : Finset ι) :
    v S ≥ v ∅ + ∑ i ∈ S, (v {i} - v ∅) := by sorry
end ZeroFreeRRG.Hardcore
