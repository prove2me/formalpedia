-- Prove2me | Definitions.Def_Geometry_KernelPatterns_Stirling
-- name    : Geometry_KernelPatterns_Stirling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:36:35.624173+00:00
-- url     : https://prove2.me/theorems/aa4841dc-91d7-4740-b43b-f9ea768b7904
-- title:
--   Aether Catalog definitions — Geometry_KernelPatterns_Stirling
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KernelPatterns.Stirling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KernelPatterns/Stirling.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell

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

namespace Geometry.KernelPatterns

open Finset

variable {n : ℕ}

/-! ### A pointwise characterisation of patterns -/



/-! ### Deleting and re-attaching the last index -/

/-- Delete the last index from a pattern on `Fin (n+1)`. -/
def restr (p : Fin (n + 1) → Fin (n + 1)) (i : Fin n) : Fin n :=
  if h : (p i.castSucc : ℕ) < n then ⟨p i.castSucc, h⟩ else i

/-- Re-attach a last index to a pattern on `Fin n`, with representative `a`. -/
def extend (q : Fin n → Fin n) (a : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) :=
  fun j => if h : (j : ℕ) < n then (q ⟨j, h⟩).castSucc else a








/-! ### How the block count changes -/





/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/






end Geometry.KernelPatterns


