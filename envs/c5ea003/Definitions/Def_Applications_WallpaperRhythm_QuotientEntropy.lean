-- Prove2me | Definitions.Def_Applications_WallpaperRhythm_QuotientEntropy
-- name    : Applications_WallpaperRhythm_QuotientEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:20.6543+00:00
-- url     : https://prove2.me/theorems/c37b0682-6de9-4717-b740-1b011c7c278e
-- title:
--   Aether Catalog definitions — Applications_WallpaperRhythm_QuotientEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.WallpaperRhythm.QuotientEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/WallpaperRhythm/QuotientEntropy.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/

/-!
# Symmetry quotients and the information content of rhythmic patterns

A binary musical pattern whose cells are identified by symmetry is constant on
symmetry classes. This file proves that such patterns are exactly Boolean
functions on the quotient. Consequently, if there are `m` symmetry classes,
there are exactly `2^m` admissible patterns.

The result is phrased for an arbitrary setoid. A group action, mirror
identifications, or a crystallographic orbit relation can each supply that
setoid. Thus the same theorem connects orbit spaces from symmetry theory with
binary information capacity in music and coding theory.
-/

namespace WallpaperRhythm

/-- Binary patterns on `α` which are constant on every equivalence class of `s`. -/
def InvariantPattern (α : Type*) (s : Setoid α) :=
  {f : α → Bool // ∀ a b, a ≈ b → f a = f b}

namespace InvariantPattern

variable {α : Type*} (s : Setoid α)

/-- Pull a Boolean labeling of the orbit space back to an invariant pattern. -/
noncomputable def quotientEquiv :
    (Quotient s → Bool) ≃ InvariantPattern α s where
  toFun f :=
    ⟨fun a => f (Quotient.mk s a), fun a b hab =>
      congrArg f (Quotient.sound hab)⟩
  invFun f := Quotient.lift f.1 (fun a b hab => f.2 a b hab)
  left_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ a => rfl
  right_inv f := by
    apply Subtype.ext
    funext a
    rfl


noncomputable instance quotientFintype [Fintype α] : Fintype (Quotient s) :=
  Fintype.ofFinite (Quotient s)

noncomputable instance [Fintype α] : Fintype (InvariantPattern α s) := by
  classical
  exact Fintype.ofEquiv (Quotient s → Bool) (quotientEquiv s)



end InvariantPattern

/-! ## A concrete musical consequence -/

/-- The indiscrete relation models maximal symmetry: every cell lies in one
orbit, so every invariant rhythm is constant. -/
def maximalSymmetrySetoid (α : Type*) : Setoid α where
  r _ _ := True
  iseqv := by
    constructor <;> simp_all


end WallpaperRhythm


