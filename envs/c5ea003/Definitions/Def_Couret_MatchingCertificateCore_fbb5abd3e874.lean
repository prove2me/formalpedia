-- Prove2me | Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874
-- name    : Couret_MatchingCertificateCore_fbb5abd3e874
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:12.634705+00:00
-- url     : https://prove2.me/theorems/efe128a5-a818-46e9-af0b-4dcc9236d67c
-- title:
--   Integral matching certificates on six coordinates
-- statement:
--   Defines integer six-vectors, coordinate basis vectors, seven formal labels including zero, and left/right lists of six pair-sum terms. A cross or mixed matching creates relation rows from doubled-label equations and matched differences. Certificates give a permutation, two label indices, and integer coefficients; validity checks a linear combination yielding the difference of distinct labels. The reverse permutation is treated separately in cross validity.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingCertificateCore.lean; source file SHA-256 724d876deede1f52a8aeb641e2c00473de595d1d0f0a9a8d4d016bce9264e3ba

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity

abbrev Vec := Fin 6 → ℤ

def basis (n : ℕ) : Vec := fun k => if k.val = n then 1 else 0
def label (n : ℕ) : Vec := if n = 0 then 0 else basis (n-1)

def leftTerms : List Vec :=
  [basis 0,basis 1,basis 2,basis 0+basis 1,basis 0+basis 2,basis 1+basis 2]
def rightTerms : List Vec :=
  [basis 3,basis 4,basis 5,basis 3+basis 4,basis 3+basis 5,basis 4+basis 5]

def relations (mixed : Bool) (p : List ℕ) : List Vec :=
  let left := if mixed then leftTerms ++ [(2:ℤ) • basis 0] else leftTerms
  let right := if mixed then rightTerms ++ [(2:ℤ) • basis 3] else rightTerms
  let diag := if mixed then
      [(2:ℤ) • (basis 0-basis 1),(2:ℤ) • (basis 3-basis 4),(2:ℤ) • (basis 2-basis 5)]
    else [(2:ℤ) • (basis 0-basis 3),(2:ℤ) • (basis 1-basis 4),(2:ℤ) • (basis 2-basis 5)]
  diag ++ ((left.zip p).map fun (v,j) => v - right[j]!)

structure Certificate where
  perm : List ℕ
  i : ℕ
  j : ℕ
  coeff : List ℤ

def combination (rows : List Vec) (coeff : List ℤ) : Vec :=
  ((rows.zip coeff).map fun (v,c) => c • v).sum

def valid (mixed : Bool) (c : Certificate) : Bool :=
  decide (c.i < c.j ∧ c.j < 7 ∧
    c.coeff.length = (relations mixed c.perm).length ∧
    combination (relations mixed c.perm) c.coeff = label c.i - label c.j)

def reversePerm : List ℕ := [5,4,3,2,1,0]
def crossValid (c : Certificate) : Bool := decide (c.perm = reversePerm) || valid false c

end Couret.InterIA.SingletonNecessity


