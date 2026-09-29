-- Prove2me | Theorems.Thm_MegaSphere_constTower_invLimit_eq
-- name    : MegaSphere.constTower_invLimit_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:08:00.403986+00:00
-- url     : https://prove2.me/theorems/ddfe049f-83e2-4660-9d11-c21bf8a12abe
-- title:
--   The inverse limit of the constant tower is exactly the diagonal: coherent
-- statement:
--   The inverse limit of the constant tower is exactly the diagonal: coherent
--   sequences are the constant sequences.
--
--   ```lean
--   theorem MegaSphere.constTower_invLimit_eq(G : Type u) [AddGroup G] :
--       (invLimit (X := fun _ => G) (constTower G)).carrier
--         = {x : ℕ → G | ∀ n, x n = x 0} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MegaSphereInverseLimit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MegaSphereInverseLimit.lean#L109

-- Thm stub generated from Novelty/MegaSphereInverseLimit.lean
import Mathlib
import Definitions.Def_Novelty_MegaSphereInverseLimit

/-!
# The Mega-Sphere I: Inverse limits of towers

The guiding fantasy of this project is a *single algebraic object* whose
projections recover every finite stage of an infinite tower at once — the
"all dimensions at once" object.  The rigorous heart of that fantasy is the
**inverse limit** of a tower

  `⋯ → X (n+1) --π n--> X n → ⋯ → X 1 → X 0`,

the universal object equipped with compatible projections to every stage.

This file builds the inverse limit of a tower of (additive) groups and of rings
completely by hand, as a sub-object of the product, and proves:

* `MegaSphere.invLimit` / `MegaSphere.invLimitRing` — the inverse limit exists
  as a concrete subgroup / subring of `∀ n, X n`.
* `MegaSphere.proj`, `MegaSphere.proj_comp` — the projections to every stage,
  and their compatibility with the connecting maps `π`.
* `MegaSphere.univMap`, `MegaSphere.proj_univMap`, `MegaSphere.univMap_unique`
  — the **universal property**: any cone over the tower factors uniquely through
  the inverse limit.  This is the precise sense in which the mega-object "is" the
  inverse limit.

Two concrete towers illustrate the two extremes:

* `MegaSphere.constTower_invLimit_eq` — the constant tower `X n = G` (identity
  connecting maps) has inverse limit the diagonal copy of `G`.
* `MegaSphere.doublingTower_invLimit_eq_bot` — the doubling tower
  `ℤ ←×2— ℤ ←×2— ⋯` **collapses**: its inverse limit is trivial, because an
  integer divisible by every power of `2` must vanish.
* `MegaSphere.padicTower_nontrivial` — by contrast the `2`-adic tower
  `ZMod (2^(n+1))` with reduction maps has a genuinely nontrivial inverse limit
  (the `2`-adic integers), a *bona fide* mega-object.
-/

open MegaSphere

universe u v

variable {X : ℕ → Type u} {Y : Type v}

/-! ## Inverse limit of a tower of additive groups -/









/-! ## Example: the constant tower recovers its base -/

theorem MegaSphere.constTower_invLimit_eq(G : Type u) [AddGroup G] :
    (invLimit (X := fun _ => G) (constTower G)).carrier
      = {x : ℕ → G | ∀ n, x n = x 0} := by sorry
