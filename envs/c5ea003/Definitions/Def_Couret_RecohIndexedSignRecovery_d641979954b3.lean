-- Prove2me | Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3
-- name    : Couret_RecohIndexedSignRecovery_d641979954b3
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:40.067582+00:00
-- url     : https://prove2.me/theorems/9c4e5f45-74b3-4c97-9e12-1b2d23e217de
-- title:
--   Indexed recovery from binary comparison signs
-- statement:
--   An additive equivalence $e:G[2]\cong\mathbb F_2^J$ converts a Boolean comparison vector to a torsion shift: true is encoded as zero and false as one, then $e^{-1}$ recovers the shift. A support is recovered by translating by the shift obtained from its own comparison vector.
--
--   This separates exact executable sign tests from the abstract two-torsion coordinate map, without enumerating all torsion translations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohIndexedSignRecovery.lean; source file SHA-256 6a312e1bf2f40ac5dd2d5482310c69a9a81feff05414db884213073f5fd0d01e

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9

set_option autoImplicit false

/-!
Sign recovery indexed by the actual cyclic coordinates.

The index type is arbitrary.  Thus a computable coordinate equivalence can
use the subtype of even cyclic factors directly, without a chosen bijection
to Fin r.  The definitions below need neither an enumeration of the ambient
group nor a Fintype instance on the coordinate index.  Complex values occur
only in their correctness statements.
-/

namespace Couret.STROBO2TORS

variable {G J : Type*} [AddCommGroup G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recover torsion coordinates at their own index type. -/
def recohIndexedRecoverTranslation
    (e : H₂ ≃+ (J → ZMod 2)) (same : J → Bool) : H₂ :=
  e.symm (fun i => recohSignBitFromBool (same i))



variable [DecidableEq G]



/-- Translate a candidate by its directly recovered coordinate vector. -/
def recohIndexedRecoverSupport (e : H₂ ≃+ (J → ZMod 2))
    (same : Finset G → J → Bool) (B : Finset G) : Finset G :=
  translateSupport B (recohIndexedRecoverTranslation e (same B) : G)







end Couret.STROBO2TORS


