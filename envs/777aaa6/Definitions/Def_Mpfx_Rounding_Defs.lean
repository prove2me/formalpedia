-- Prove2me | Definitions.Def_Mpfx_Rounding_Defs
-- name    : Mpfx_Rounding_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:41:02.176942+00:00
-- url     : https://prove2.me/theorems/878aa4f8-8781-4135-82f7-4a41521f7145
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean

import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
namespace Mpfx
inductive TieBreak where
  /-- Ties to the value with even significand (IEEE `roundTiesToEven`). -/
  | toEven : TieBreak
  /-- Ties to the value with larger magnitude (IEEE `roundTiesToAway`). -/
  | awayZero : TieBreak
deriving DecidableEq, Repr
inductive RoundingMode where
  | toNegative : RoundingMode
  | toPositive : RoundingMode
  | toZero : RoundingMode
  | awayZero : RoundingMode
  | toOdd : RoundingMode
  | nearest : TieBreak → RoundingMode
deriving DecidableEq, Repr
inductive RoundResult where
  | value (v : WithSpecial Dyadic) : RoundResult
  | undefined : RoundResult
def FiniteFormat.IsUndefined (F : FiniteFormat) (rm : RoundingMode) : Prop :=
  F.p = (1 : ℕ) ∧ F.exp = ⊥ ∧
    (rm = .toOdd ∨ rm = .nearest .toEven)
structure SpecialMap (F : Format) where
  map : Special → WithSpecial Dyadic
  mem : ∀ s, map s ∈ F.values
structure OverflowMap (F : Format) where
  map : Bool → WithSpecial Dyadic
  mem : ∀ negative, map negative ∈ F.values
def IsFaithfulRound (F : FiniteFormat) (x : ℝ) (y : Dyadic) : Prop :=
  (y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)) ∨
  (y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ))
def RoundsFinite (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) :
    Prop :=
  y ∈ F ∧
  match rm with
  | .toNegative =>
      (y : ℝ) ≤ x ∧
      ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)
  | .toPositive =>
      x ≤ (y : ℝ) ∧
      ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ)
  | .toZero =>
      |(y : ℝ)| ≤ |x| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |(z : ℝ)| ≤ |x| → (z : ℝ) * x ≥ 0 →
        |(z : ℝ)| ≤ |(y : ℝ)|
  | .awayZero =>
      |x| ≤ |(y : ℝ)| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |x| ≤ |(z : ℝ)| → (z : ℝ) * x ≥ 0 →
        |(y : ℝ)| ≤ |(z : ℝ)|
  | .toOdd =>
      IsFaithfulRound F x y ∧
      (x ≠ (y : ℝ) → F.IsOdd y)
  | .nearest .toEven =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      ((∃ z : Dyadic, z ∈ F ∧ IsFaithfulRound F x z ∧
          z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) → F.IsEven y)
  | .nearest .awayZero =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
          z ≠ y → |x - (y : ℝ)| = |x - (z : ℝ)| → |(z : ℝ)| ≤ |(y : ℝ)|)
def RoundsInBound (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) : Prop :=
  RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y
def Overflows (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) : Prop :=
  ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y
def Rounds (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    (rm : RoundingMode) : WithSpecial ℝ → RoundResult → Prop
  | .special s, r => r = .value (S.map s)
  | .finite _, .undefined => F.IsUndefined rm
  | .finite x, .value v =>
      ¬ F.IsUndefined rm ∧ ∃ y, RoundsFinite F.unbounded rm x y ∧
        ((Format.boundOK F.b y ∧ v = .finite y) ∨
         (¬ Format.boundOK F.b y ∧ v = O.map (decide ((y : ℚ) < 0))))
end Mpfx


