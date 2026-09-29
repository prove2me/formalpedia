-- Prove2me | solution 1 for Geometry.KernelPatterns.mem_patternsWith
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:32:52.307819+00:00
-- url     : https://prove2.me/submissions/2ae771f7-f228-48c2-9387-9330edc790ee

-- Sol generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling

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
theorem solution{n k : ℕ} (p : Fin n → Fin n) :
    p ∈ patternsWith n k ↔ pat p = p ∧ (univ.image p).card = k := by
  simp [patternsWith, mem_patterns_self]
