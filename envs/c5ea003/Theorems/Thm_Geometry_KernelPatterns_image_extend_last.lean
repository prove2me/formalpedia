-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_image_extend_last
-- name    : Geometry.KernelPatterns.image_extend_last
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:16:14.454915+00:00
-- url     : https://prove2.me/theorems/b41046b9-8fb6-4374-baef-ef1e9d059301
-- title:
--   Image extend last
-- statement:
--   Formal statement of `Geometry.KernelPatterns.image_extend_last` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Geometry.KernelPatterns.image_extend_last(q : Fin n → Fin n) :
--       univ.image (extend q (Fin.last n)) =
--         (univ.image q).image Fin.castSucc ∪ {Fin.last n} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Stirling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Stirling.lean#L136

-- Thm stub generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
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

theorem Geometry.KernelPatterns.image_extend_last(q : Fin n → Fin n) :
    univ.image (extend q (Fin.last n)) =
      (univ.image q).image Fin.castSucc ∪ {Fin.last n} := by sorry
