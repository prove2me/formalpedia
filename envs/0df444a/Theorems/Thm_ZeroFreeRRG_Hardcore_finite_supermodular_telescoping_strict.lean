-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_finite_supermodular_telescoping_strict
-- name    : ZeroFreeRRG.Hardcore.finite_supermodular_telescoping_strict
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:23:34.166896+00:00
-- url     : https://prove2.me/theorems/d148976f-65bd-41f4-a3e7-4a58a182ca7c
-- title:
--   Strict supermodular telescoping from one positive mixed difference
-- statement:
--   For a real set function with nonnegative mixed insertion differences, suppose the mixed difference of distinct $i,j$ at the empty set is strictly positive. Then the finite telescoping inequality is strict for every set containing $i$ and $j$. This supplies the strict-event step of the hardcore size-bias argument.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open scoped BigOperators

namespace ZeroFreeRRG.Hardcore
theorem finite_supermodular_telescoping_strict {ι : Type} [DecidableEq ι] (v : Finset ι → ℝ)
    (hSM : ∀ S : Finset ι, ∀ i j, i ∉ S → j ∉ S → i ≠ j →
      v (insert i (insert j S)) + v S ≥ v (insert i S)+v (insert j S))
    (T : Finset ι) (i j : ι) (hi : i ∉ T) (hj : j ∉ T) (hij : i ≠ j)
    (hstrict : v {i,j} + v ∅ > v {i} + v {j}) :
    v (insert i (insert j T)) > v ∅ + ∑ a ∈ insert i (insert j T), (v {a} - v ∅) := by sorry
end ZeroFreeRRG.Hardcore
