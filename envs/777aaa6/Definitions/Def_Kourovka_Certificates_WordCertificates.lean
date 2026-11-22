-- Prove2me | Definitions.Def_Kourovka_Certificates_WordCertificates
-- name    : Kourovka_Certificates_WordCertificates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:40:55.199732+00:00
-- url     : https://prove2.me/theorems/b50d1fb3-e4d0-4972-9dca-942eb20d8d5e
-- title:
--   Word Certificates
-- statement:
--   Definitions and structural lemmas for Word Certificates, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/WordCertificates.lean

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.WordCertificates
abbrev Word (n : ℕ) := List (Fin n × Bool)
inductive Derivation (n : ℕ) where
  | one
  | relator (w : Word n)
  | mul (left right : Derivation n)
  | inv (body : Derivation n)
  | conjugate (w : Word n) (body : Derivation n)
  deriving DecidableEq
def Derivation.eval {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Derivation n → FreeGroup (Fin n)
  | .one => 1
  | .relator w => if FreeGroup.mk w ∈ rels then FreeGroup.mk w else 1
  | .mul left right => left.eval rels * right.eval rels
  | .inv body => (body.eval rels)⁻¹
  | .conjugate w body => FreeGroup.mk w * body.eval rels * (FreeGroup.mk w)⁻¹
def derivableSubgroup {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Subgroup (FreeGroup (Fin n)) where
  carrier := {r | ∃ d : Derivation n, d.eval rels = r}
  one_mem' := ⟨.one, rfl⟩
  mul_mem' := by
    rintro a b ⟨da, rfl⟩ ⟨db, rfl⟩
    exact ⟨.mul da db, rfl⟩
  inv_mem' := by
    rintro a ⟨da, rfl⟩
    exact ⟨.inv da, rfl⟩
instance derivableSubgroup_normal {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    (derivableSubgroup rels).Normal where
  conj_mem := by
    rintro a ⟨da, rfl⟩ g
    refine ⟨.conjugate g.toWord da, ?_⟩
    simp only [Derivation.eval, FreeGroup.mk_toWord]
def checkWord {n : ℕ} (rels : List (FreeGroup (Fin n))) (w : Word n)
    (d : Derivation n) : Bool := decide (d.eval rels = FreeGroup.mk w)
end Kourovka.MetabelianEnumeration.WordCertificates


