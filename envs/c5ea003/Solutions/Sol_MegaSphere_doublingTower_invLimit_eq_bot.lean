-- Prove2me | solution 1 for MegaSphere.doublingTower_invLimit_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:39:48.343806+00:00
-- url     : https://prove2.me/submissions/b6440860-548c-43d8-ad82-d83ba4e0c9df

-- Sol generated from Novelty/MegaSphereInverseLimit.lean
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



/-! ## Example: the doubling tower collapses -/



/-- An integer divisible by every power of two is zero. -/
theorem int_eq_zero_of_forall_two_pow_dvd {a : ℤ} (h : ∀ n : ℕ, (2 : ℤ) ^ n ∣ a) :
    a = 0 := by
  by_contra ha
  have hpos : (0 : ℤ) < |a| := abs_pos.mpr ha
  have hdvd : (2 : ℤ) ^ a.natAbs ∣ a := h a.natAbs
  have hdvd' : (2 : ℤ) ^ a.natAbs ∣ |a| := (dvd_abs _ _).mpr hdvd
  have hle : (2 : ℤ) ^ a.natAbs ≤ |a| := Int.le_of_dvd hpos hdvd'
  have habs : |a| = (a.natAbs : ℤ) := Int.abs_eq_natAbs a
  have hlt : (a.natAbs : ℤ) < (2 : ℤ) ^ a.natAbs := by exact_mod_cast Nat.lt_two_pow_self
  rw [habs] at hle
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)


/-! ## Inverse limit of a tower of rings, and a nontrivial mega-object -/








open MegaSphere in
theorem solution:
    invLimit (X := fun _ => ℤ) dbl = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  rintro x hx
  -- `hx m : 2 * x (m+1) = x m`.
  have hx' : ∀ m, 2 * x (m + 1) = x m := fun m => hx m
  -- For all m and k, `x m = 2^k * x (m+k)`.
  have key : ∀ m k, x m = 2 ^ k * x (m + k) := by
    intro m k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [ih]
        have := hx' (m + j)
        rw [pow_succ]
        rw [mul_assoc, ← this]
        ring_nf
  -- Hence every `x m = 0`.
  funext m
  show x m = 0
  apply int_eq_zero_of_forall_two_pow_dvd
  intro k
  exact ⟨x (m + k), key m k⟩
