-- Prove2me | Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
-- name    : Kourovka_Certificates_IsomorphismSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:44.063181+00:00
-- url     : https://prove2.me/theorems/5cee6e48-dda4-4659-9f8f-0a5eb9a62459
-- title:
--   Isomorphism Semantics
-- statement:
--   Definitions and structural lemmas for Isomorphism Semantics, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/IsomorphismSemantics.lean

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
def GoodMaps (pq : PresentationCode × PresentationCode) (fg : Maps) : Prop :=
  (∀ w ∈ pq.1.2, Good (pq.2, substitute fg.1 w)) ∧
    (∀ w ∈ pq.2.2, Good (pq.1, substitute fg.2 w)) ∧
      (∀ i < pq.1.1, Good (pq.1, substitute fg.2 (fg.1.getD i []) ++ [(i, false)])) ∧
        (∀ i < pq.2.1, Good (pq.2, substitute fg.1 (fg.2.getD i []) ++ [(i, false)]))
def encodeImages {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) : Images :=
  List.ofFn fun i => WordCertificates.encodeWord (f i).toWord
end Kourovka.MetabelianEnumeration.ComputableIsomorphism


