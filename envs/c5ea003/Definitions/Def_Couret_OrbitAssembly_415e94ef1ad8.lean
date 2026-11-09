-- Prove2me | Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8
-- name    : Couret_OrbitAssembly_415e94ef1ad8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:09:04.59818+00:00
-- url     : https://prove2.me/theorems/5ae61012-578a-4652-88dd-093bde283a47
-- title:
--   Projected orbit shape of a two-point exchange
-- statement:
--   Defines a structural predicate for two supports in $\mathbb Z/(2m)\mathbb Z$: each difference is an antipodal pair and the intersection has two distinct points separated from the exchanged points after projection modulo $m$. The projected displacement has order two or four, with the corresponding explicitly prescribed common-point configuration.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitAssembly.lean; source file SHA-256 d6824040ee0d4b903b0ade8b6cd64bca166fac4d10f9c9e004600456bf0ae193

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Parity





/-- The quotient orbit classification retains the original geometric witnesses. -/
def OrbitShape (m : ℕ) (S T : Finset (ZMod (2*m))) : Prop :=
  ∃ a b c d : ZMod (2*m),
    S \ T=fibre (m : ZMod (2*m)) a ∧
    T \ S=fibre (m : ZMod (2*m)) b ∧
    c ≠ d ∧ S ∩ T={c,d} ∧
    projection m c ≠ projection m a ∧ projection m c ≠ projection m b ∧
    projection m d ≠ projection m a ∧ projection m d ≠ projection m b ∧
    ((addOrderOf (projection m (b-a))=2 ∧
        projection m d=projection m c+projection m (b-a)) ∨
      (addOrderOf (projection m (b-a))=4 ∧
        ((projection m c=projection m a+2 • projection m (b-a) ∧
          projection m d=projection m a+3 • projection m (b-a)) ∨
         (projection m c=projection m a+3 • projection m (b-a) ∧
          projection m d=projection m a+2 • projection m (b-a)))))





end Couret.InterIA.Catalogue.Orbits


