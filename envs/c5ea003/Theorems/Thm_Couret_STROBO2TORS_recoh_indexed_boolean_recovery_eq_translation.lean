-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_eq_translation
-- name    : Couret.STROBO2TORS.recoh_indexed_boolean_recovery_eq_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:46:03.716342+00:00
-- url     : https://prove2.me/theorems/08a8b415-c3cb-413d-9e74-b553a9a40a1d
-- title:
--   Boolean equality bits recover the exact torsion translation
-- statement:
--   Let $G$ be an abelian group, $J$ an arbitrary index type, and $H=G[2]$. Let $(\chi_i)_{i\in J}$ be complex additive characters and $e:H\simeq(J\to\mathbb F_2)$ an additive equivalence with $\chi_i(v)=1$ when $e(v)_i=0$ and $\chi_i(v)=-1$ otherwise. For a finite support $B$, write $P_i(B)=\sum_{x\in B}\chi_i(x)$ and assume $P_i(B)\ne0$ for every $i$. Fix $u\in H$ and Booleans $s_i$ satisfying $s_i=\mathrm{true}\iff P_i(B+u)=P_i(B)$. Encode true as $0$ and false as $1$, obtaining a vector $b\in J\to\mathbb F_2$. Then $$e^{-1}(b)=u.$$ This is the equality asserted by the indexed translation-recovery function. No finiteness of $G$ or $J$ and no three-element condition on $B$ is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohIndexedSignRecovery.lean, lines 33–49; source file SHA-256 6a312e1bf2f40ac5dd2d5482310c69a9a81feff05414db884213073f5fd0d01e; theorem Couret.STROBO2TORS.recoh_indexed_boolean_recovery_eq_translation

import Aesop
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_recovered_sign_bit_of_sign
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_bit_from_bool_eq
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





variable [DecidableEq G]

theorem recoh_indexed_boolean_recovery_eq_translation
    (bank : J → AddChar G ℂ) (e : H₂ ≃+ (J → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : J),
      bank i (u : G) = if e u i = 0 then 1 else -1)
    (B : Finset G) (hnonzero : ∀ i, recohSupportProbe (bank i) B ≠ 0)
    (u : H₂) (same : J → Bool)
    (hsame : ∀ i, same i = true ↔
      recohSupportProbe (bank i) (translateSupport B (u : G)) =
        recohSupportProbe (bank i) B) :
    recohIndexedRecoverTranslation e same = u := by sorry










end Couret.STROBO2TORS
