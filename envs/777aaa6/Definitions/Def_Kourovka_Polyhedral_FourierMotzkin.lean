-- Prove2me | Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
-- name    : Kourovka_Polyhedral_FourierMotzkin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:40:55.660226+00:00
-- url     : https://prove2.me/theorems/aaa125e2-27d8-4c4a-b63b-15b46add3d95
-- title:
--   Fourier Motzkin
-- statement:
--   Definitions and structural lemmas for Fourier Motzkin, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean

import Definitions.Def_Kourovka_Presentations_Presentations
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ
  deriving DecidableEq
def Row.eval {n : ℕ} (r : Row n) {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Fin n → K) : K :=
  (∑ i, (r.coeff i : K) * x i) + (r.constant : K)
def Satisfies {n : ℕ} (rows : List (Row n)) {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Fin n → K) : Prop :=
  ∀ r ∈ rows, r.eval x ≤ 0
def Feasible {n : ℕ} (rows : List (Row n)) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Prop := ∃ x : Fin n → K, Satisfies rows x
def Row.head {n : ℕ} (r : Row (n + 1)) : ℚ := r.coeff 0
def Row.tail {n : ℕ} (r : Row (n + 1)) : Row n :=
  ⟨fun i => r.coeff i.succ, r.constant⟩
def Row.combine {n : ℕ} (l u : Row (n + 1)) : Row n :=
  ⟨fun i => u.head * l.coeff i.succ - l.head * u.coeff i.succ,
    u.head * l.constant - l.head * u.constant⟩
def negatives {n : ℕ} (rows : List (Row (n + 1))) : List (Row (n + 1)) :=
  rows.filter fun r => r.head < 0
def positives {n : ℕ} (rows : List (Row (n + 1))) : List (Row (n + 1)) :=
  rows.filter fun r => 0 < r.head
def eliminate {n : ℕ} (rows : List (Row (n + 1))) : List (Row n) :=
  (rows.filter (fun r => r.head = 0)).map Row.tail ++
    (negatives rows).flatMap fun l => (positives rows).map (Row.combine l)
def check : (n : ℕ) → List (Row n) → Bool
  | 0, rows => rows.all fun r => r.constant ≤ 0
  | n + 1, rows => check n (eliminate rows)
end Kourovka.MetabelianEnumeration.FourierMotzkin


