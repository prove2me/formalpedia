-- Prove2me | Definitions.Def_Kourovka_Polyhedral_ConeVerifier
-- name    : Kourovka_Polyhedral_ConeVerifier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:43.767412+00:00
-- url     : https://prove2.me/theorems/f66b18ad-d73f-4790-a870-003a7dfb15f7
-- title:
--   Cone Verifier
-- statement:
--   Definitions and structural lemmas for Cone Verifier, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeVerifier.lean

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
abbrev Vec (n : ℕ) := Fin n → ℚ
abbrev Supports (n : ℕ) := List (List (Vec n))
def dot {n : ℕ} (u : Vec n) (x : Fin n → ℝ) : ℝ := ∑ i, (u i : ℝ) * x i
def supportRow {n : ℕ} (u : Vec n) (epsilon : ℚ) : Row n := ⟨u, -epsilon⟩
def search (n : ℕ) (epsilon : ℚ) : Supports n → List (Row n) → Bool
  | [], rows => check n rows
  | support :: rest, rows =>
    support.any fun u => search n epsilon rest (supportRow u epsilon :: rows)
def coordinate {n : ℕ} (i : Fin n) (a b : ℚ) : Row n :=
  ⟨fun j => if j = i then a else 0, b⟩
def cubeRows (n : ℕ) : List (Row n) :=
  (List.finRange n).flatMap fun i => [coordinate i 1 (-1), coordinate i (-1) (-1)]
def faceRows {n : ℕ} (i : Fin n) (sign : ℚ) : List (Row n) :=
  [coordinate i 1 (-sign), coordinate i (-1) sign] ++ cubeRows n
def CubeSphere {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ ∃ i, x i = -1 ∨ x i = 1
def badDirection {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Bool :=
  (List.finRange n).any fun i =>
    ([-1, 1] : List ℚ).any fun sign => search n epsilon supports (faceRows i sign)
def CubeMargin {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Prop :=
  ∀ x : Fin n → ℝ, CubeSphere x →
    ∃ support ∈ supports, ∀ u ∈ support, (epsilon : ℝ) < dot u x
def checkMargin {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Bool :=
  !(badDirection supports epsilon)
def ConeCover {n : ℕ} (supports : Supports n) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → ∃ support ∈ supports, ∀ u ∈ support, 0 < dot u x
end Kourovka.MetabelianEnumeration.ConeVerifier


