-- Prove2me | Theorems.Thm_BookSixth_round_circle_snoc_motion_extension
-- name    : BookSixth.round_circle_snoc_motion_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-03T13:34:52.281975+00:00
-- url     : https://prove2.me/theorems/21cbdeca-bd59-4460-b1f3-bc13d255eec6
-- title:
--   Extending a roundness preserving motion by one unlinked circle
-- statement:
--   Suppose the first n circles have already been carried to their separated standard positions by an ambient isotopy that keeps each of them round at every time. If one further round circle is disjoint from each of them and is individually unlinked with each prefix component, then there is an ambient isotopy for the enlarged family that reaches all standard positions and keeps every component round throughout. This is the one step needed to build the finite family motion by induction, and isolates the geometric extension across the last component.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, pp. 99-103; relative one-component extension step in the spherical-dome construction.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_snoc_motion_extension {n : Nat}
    (C : Fin (n + 1) -> Set Space3)
    (P : Real -> Homeomorph Space3 Space3)
    (hP :
      Continuous (fun p : Prod Real Space3 => P p.1 p.2) /\
      Continuous (fun p : Prod Real Space3 => (P p.1).symm p.2) /\
      (forall x, P 0 x = x) /\
      (forall i : Fin n, Set.image (P 1) (C i.castSucc) = standardCircle i.val) /\
      (forall (t : Real) (i : Fin n), RoundCircle (Set.image (P t) (C i.castSucc))))
    (hroundD : RoundCircle (C (Fin.last n)))
    (hdisjointD : forall i : Fin n, Disjoint (C i.castSucc) (C (Fin.last n)))
    (hpairsD : forall i : Fin n, IsUnlink (![C i.castSucc, C (Fin.last n)] : Fin 2 -> Set Space3)) :
    Exists fun K : Real -> Homeomorph Space3 Space3 =>
      Continuous (fun p : Prod Real Space3 => K p.1 p.2) /\
      Continuous (fun p : Prod Real Space3 => (K p.1).symm p.2) /\
      (forall x, K 0 x = x) /\
      (forall i : Fin (n + 1), Set.image (K 1) (C i) = standardCircle i.val) /\
      (forall (t : Real) (i : Fin (n + 1)), RoundCircle (Set.image (K t) (C i))) := by sorry
