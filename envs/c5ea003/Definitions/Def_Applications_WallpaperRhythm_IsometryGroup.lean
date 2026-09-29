-- Prove2me | Definitions.Def_Applications_WallpaperRhythm_IsometryGroup
-- name    : Applications_WallpaperRhythm_IsometryGroup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:21.5472+00:00
-- url     : https://prove2.me/theorems/40753079-3346-4831-9fb8-24167b5d4f56
-- title:
--   Aether Catalog definitions — Applications_WallpaperRhythm_IsometryGroup
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WallpaperRhythm.IsometryGroup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WallpaperRhythm/IsometryGroup.lean by skeleton subtraction
import Mathlib

/-!
# The isometry group of a rhythm line (the 1-dimensional crystallographic group)

The full symmetry group of a rhythm `f : ℤ → Bool` is not just its translations:
it also includes **reflections** (palindromes) and, in general, the isometries of
the integer time-line that preserve the onset pattern.  The isometries of `ℤ`
form the **infinite dihedral group** `Dih∞`, the 1-dimensional analogue of a
wallpaper group.

We realise isometries concretely as permutations of `ℤ` of the affine form
`x ↦ ±x + t`.

* `isomGroup : Subgroup (Equiv.Perm ℤ)` — the isometry group of the line.
* `transl`, `refl` — the two basic families of isometries (translations and the
  reflection through the origin), both shown to be isometries.
* `sign` — the orientation homomorphism `isomGroup → {±1}`, giving the extension
  `1 → ℤ (translations) → Dih∞ → ℤ/2 → 1`.
* `refl_mul_refl_eq_transl` — **the product of two reflections is a translation**,
  the defining relation of the infinite dihedral group.
* `symmGroup f` — the isometries preserving a rhythm `f`, a subgroup; and
  `crystalGroup f` — its intersection with the isometries: the rhythm's genuine
  crystallographic symmetry group.
* `refl_mem_symmGroup_iff` — a rhythm is a **palindrome** exactly when the origin
  reflection preserves it; `transl_mem_symmGroup_iff` — a translation preserves it
  exactly when it is a period.
-/

namespace WallpaperRhythm

open Equiv

/-- A rhythm: a Boolean onset function on the integer time-line. -/
abbrev Rhythm := ℤ → Bool

/-! ## The isometry group of the line -/

/-- The isometry group of `ℤ`: permutations of the form `x ↦ ±x + t`.
This is a concrete model of the infinite dihedral group `Dih∞`. -/
def isomGroup : Subgroup (Equiv.Perm ℤ) where
  carrier := {e | ∃ (s : Bool) (t : ℤ), ∀ x, e x = (if s then -x else x) + t}
  one_mem' := ⟨false, 0, fun x => by simp⟩
  mul_mem' := by
    rintro e1 e2 ⟨s1, t1, h1⟩ ⟨s2, t2, h2⟩
    refine ⟨xor s1 s2, (if s1 then -t2 else t2) + t1, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, h1 (e2 x), h2 x]
    cases s1 <;> cases s2 <;> simp <;> ring
  inv_mem' := by
    rintro e ⟨s, t, h⟩
    refine ⟨s, if s then t else -t, fun x => ?_⟩
    apply e.injective
    have hcoe : (e⁻¹ : Equiv.Perm ℤ) x = e.symm x := rfl
    rw [hcoe, Equiv.apply_symm_apply, h]
    cases s <;> simp

/-- A translation `x ↦ x + t` as an isometry. -/
def transl (t : ℤ) : Equiv.Perm ℤ := Equiv.addRight t

/-- The reflection `x ↦ -x` through the origin. -/
def refl : Equiv.Perm ℤ := Equiv.neg ℤ




/-- A reflection through the point `t/2`: `x ↦ -x + t`. -/
def reflAt (t : ℤ) : Equiv.Perm ℤ := refl.trans (transl t)



/-! ## The orientation homomorphism -/

/-- The orientation ("sign") of an isometry, `+1` for translations and `-1` for
reflections.  Read off as `e 1 - e 0`. -/
def sign (e : Equiv.Perm ℤ) : ℤ := e 1 - e 0







/-! ## The symmetry group of a rhythm -/

/-- The isometries preserving a rhythm `f` (`f (e n) = f n` for all `n`) form a
subgroup of `Perm ℤ`. -/
def symmGroup (f : Rhythm) : Subgroup (Equiv.Perm ℤ) where
  carrier := {e | ∀ n, f (e n) = f n}
  one_mem' := by intro n; simp
  mul_mem' := by
    intro a b ha hb n
    rw [Equiv.Perm.mul_apply, ha (b n), hb n]
  inv_mem' := by
    intro a ha n
    have hcoe : (a⁻¹ : Equiv.Perm ℤ) n = a.symm n := rfl
    have := ha (a.symm n)
    rw [Equiv.apply_symm_apply] at this
    rw [hcoe, this]


/-- **The crystallographic symmetry group of a rhythm**: the isometries of the
line that preserve its onset pattern.  This is the object the wallpaper-group
programme classifies. -/
def crystalGroup (f : Rhythm) : Subgroup (Equiv.Perm ℤ) := isomGroup ⊓ symmGroup f





end WallpaperRhythm


