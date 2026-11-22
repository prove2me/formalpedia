-- Prove2me | Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
-- name    : Kourovka_Certificates_PresentationIsomorphism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:27.986408+00:00
-- url     : https://prove2.me/theorems/7b4af226-48c7-4964-8b4d-1c5d9c985e51
-- title:
--   Presentation Isomorphism
-- statement:
--   Definitions and structural lemmas for Presentation Isomorphism, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean

import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.WordCertificates
def relSet {n : ℕ} (rels : List (FreeGroup (Fin n))) : Set (FreeGroup (Fin n)) :=
  {r | r ∈ rels}
structure MapsCertificate {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m))) where
  forward : Fin n → Word m
  backward : Fin m → Word n
  sourceProof : Fin source.length → Derivation m
  targetProof : Fin target.length → Derivation n
  sourceInverse : Fin n → Derivation n
  targetInverse : Fin m → Derivation m
def MapsCertificate.forwardMap {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) :=
  FreeGroup.lift (fun i => FreeGroup.mk (cert.forward i))
def MapsCertificate.backwardMap {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) :=
  FreeGroup.lift (fun i => FreeGroup.mk (cert.backward i))
def MapsCertificate.check {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) : Bool :=
  decide (
    (∀ i : Fin source.length,
      (cert.sourceProof i).eval target = cert.forwardMap source[i]) ∧
    (∀ i : Fin target.length,
      (cert.targetProof i).eval source = cert.backwardMap target[i]) ∧
    (∀ i : Fin n, (cert.sourceInverse i).eval source =
      cert.backwardMap (FreeGroup.mk (cert.forward i)) * (FreeGroup.of i)⁻¹) ∧
    (∀ i : Fin m, (cert.targetInverse i).eval target =
      cert.forwardMap (FreeGroup.mk (cert.backward i)) * (FreeGroup.of i)⁻¹))
theorem lift_mapped_mk {n m : ℕ} (target : List (FreeGroup (Fin m)))
    (f : Fin n → FreeGroup (Fin m)) (w : FreeGroup (Fin n)) :
    FreeGroup.lift (fun i => PresentedGroup.mk (relSet target) (f i)) w =
      PresentedGroup.mk (relSet target) (FreeGroup.lift f w) := by
  exact (FreeGroup.lift_unique ((PresentedGroup.mk (relSet target)).comp (FreeGroup.lift f))
    (by intro i; simp)).symm
def descend {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target)) :
    PresentedGroup (relSet source) →* PresentedGroup (relSet target) :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.mk (relSet target) (f i))
    (by
      intro r hr
      rw [lift_mapped_mk]
      exact PresentedGroup.mk_eq_one_iff.mpr (h r hr))
end Kourovka.MetabelianEnumeration.WordCertificates


