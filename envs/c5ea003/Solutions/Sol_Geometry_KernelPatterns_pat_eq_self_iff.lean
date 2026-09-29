-- Prove2me | solution 1 for Geometry.KernelPatterns.pat_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:35:23.393597+00:00
-- url     : https://prove2.me/submissions/192873d2-3ac9-4ad3-ba6c-2569f5f2fce7

-- Sol generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_pat_le

/-!
# Kernel patterns with a prescribed number of blocks are the Stirling numbers

Mathlib defines the Stirling numbers of the second kind `Nat.stirlingSecond`
purely by their recursion.  Here we prove that they really do count kernel
patterns: the number of equality patterns of `n`-tuples having exactly `k`
distinct values is `Nat.stirlingSecond n k`
(`card_patternsWith_eq_stirlingSecond`).

The proof is a structural induction implemented by an explicit
restriction/extension dictionary between patterns on `Fin (n+1)` and patterns on
`Fin n`:

* `restr p` — delete the last index;
* `extend q a` — re-attach a last index whose representative is `a`;
* `extend_restr`, `restr_extend` — these are mutually inverse.

Deleting the last index either destroys a singleton block (`p` fixes the last
index) or leaves the block structure unchanged (`p` sends it into one of the
`k` existing blocks), which is exactly the Stirling recursion
`S(n+1, k+1) = (k+1) * S(n, k+1) + S(n, k)`.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}

/-! ### A pointwise characterisation of patterns -/



/-! ### Deleting and re-attaching the last index -/










/-! ### How the block count changes -/





/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/







open Geometry.KernelPatterns in
theorem solution(p : Fin n → Fin n) :
    pat p = p ↔ (∀ i, p i ≤ i) ∧ ∀ i, p (p i) = p i := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := pat_le p i
      rwa [h] at hi
    · have hi := pat_apply_pat p i
      rwa [h] at hi
  · rintro ⟨hle, hidem⟩
    funext i
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [hidem i])
    · refine Finset.le_min' _ _ _ ?_
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      calc p i = p j := hj.symm
        _ ≤ j := hle j
