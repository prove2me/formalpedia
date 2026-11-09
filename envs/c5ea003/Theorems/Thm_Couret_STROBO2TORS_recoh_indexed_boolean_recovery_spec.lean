-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_spec
-- name    : Couret.STROBO2TORS.recoh_indexed_boolean_recovery_spec
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:43.141236+00:00
-- url     : https://prove2.me/theorems/de745e46-650f-4dd6-82d6-1b5df4041c68
-- title:
--   Indexed equality Booleans give a correct translation recovery map
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Let $I,J$ be index types, $\chi_i$ a character bank, $o=(R,v)$ an observation, $\iota:J\to I$, and $e:H\cong(\mathbb Z/2\mathbb Z)^J$ additive. Assume $\chi_{\iota(j)}(u)=(-1)^{e(u)_j}$ for all $u\in H$, every selected reading is nonzero on every triple, and a Boolean $b(B,j)$ is true exactly when $v_{\iota(j)}=P_{\chi_{\iota(j)}}(B)$. Define $r(B)=B+e^{-1}((0\text{ if }b(B,j)\text{ else }1)_j)$. Then
--
--   $$|B|=3\Longrightarrow|r(B)|=3,$$
--   $$|B|=3,\ 2u=0,\ (R_{B+u},(P_{\chi_i}(B+u))_i)=o\Longrightarrow r(B)=B+u.$$
--
--   No finite-group assumption is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohIndexedSignRecovery.lean, lines 61–89; source file SHA-256 6a312e1bf2f40ac5dd2d5482310c69a9a81feff05414db884213073f5fd0d01e; theorem Couret.STROBO2TORS.recoh_indexed_boolean_recovery_spec

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_eq_translation
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

theorem recoh_indexed_boolean_recovery_spec {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (same : Finset G → J → Bool)
    (hcoord : ∀ (u : H₂) (i : J),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hsame : ∀ B i, same B i = true ↔
      obs.2 (index i) = recohSupportProbe (bank (index i)) B) :
    RecohTranslationRecoverySpec bank obs (recohIndexedRecoverSupport e same) := by sorry




end Couret.STROBO2TORS
