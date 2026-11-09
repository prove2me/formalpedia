-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_checked_decoder_eq_exact
-- name    : Couret.STROBO2TORS.recoh_indexed_checked_decoder_eq_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:21.88211+00:00
-- url     : https://prove2.me/theorems/bceaf55f-bb9d-41ac-b83b-67bf21667ff7
-- title:
--   Indexed sign recovery makes fast decoding exact
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S$ counts ordered sums and $B$ is a bank of complex additive characters. Assume $G$ finite. Let $U\subseteq G$ be finite, $h:G\to\operatorname{Option}(G)$ a sound and complete solver for $2x=t$, $B=(\chi_i)_{i\in I}$ a bank, and $o=(R,(o_i))$ an observation whose nonzero square support is contained in $U$. Let $j:J\to I$ and $e:H\simeq(J\to\mathbb F_2)$ satisfy $\chi_{j(a)}(u)=(-1)^{e(u)_a}$. Assume these selected probes are nonzero on every three-element support. Let Boolean $s(S,a)$ mean exactly $o_{j(a)}=P_{\chi_{j(a)}}(S)$, and Boolean $c(S)$ mean exactly $\mathcal O_B(S)=o$. Then $$D_{\mathrm{checked}}(U,h,\operatorname{IndexedRecover}(e,s),c)=D_B(o).$$ No injectivity premise on $j$ is added.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohIndexedSignRecovery.lean, lines 91–110; source file SHA-256 6a312e1bf2f40ac5dd2d5482310c69a9a81feff05414db884213073f5fd0d01e; theorem Couret.STROBO2TORS.recoh_indexed_checked_decoder_eq_exact

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_spec
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

theorem recoh_indexed_checked_decoder_eq_exact [Fintype G] {I : Type*}
    (U : Finset G) (half : G → Option G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (same : Finset G → J → Bool) (check : Finset G → Bool)
    (hhalf : RecohHalfSolverSpec half)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (hcoord : ∀ (u : H₂) (i : J),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hsame : ∀ B i, same B i = true ↔
      obs.2 (index i) = recohSupportProbe (bank (index i)) B)
    (hcheck : ∀ S, check S = true ↔ recohObservation bank S = obs) :
    recohCheckedFastDecoder U half (recohIndexedRecoverSupport e same) check =
      recohExactDecoder bank obs := by sorry


end Couret.STROBO2TORS
