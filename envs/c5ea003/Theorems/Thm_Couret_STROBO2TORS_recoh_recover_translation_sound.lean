-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_sound
-- name    : Couret.STROBO2TORS.recoh_recover_translation_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:34.033439+00:00
-- url     : https://prove2.me/theorems/00b0d2ed-ba10-4757-9685-2cfe0a7b25fc
-- title:
--   Sign coordinates recover the observed translation
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $B=(\chi_i)_{i<r}$ and $e:H\simeq\mathbb F_2^r$ satisfy $\chi_i(u)=(-1)^{e(u)_i}$. Let a finite support $S$ have all probes nonzero, and let complex observations $o_i$ satisfy $o_i=\pm P_{\chi_i}(S)$ independently for each index. The defined recovered $u\in H$ then satisfies $$P_{\chi_i}(S+u)=o_i\qquad(i<r).$$ No three-element assumption is required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSignRecovery.lean, lines 85–104; source file SHA-256 9c4330cb72ad0993c6c48361a0b68823a89e5af35e3cfb07799a30c9c651fb1c; theorem Couret.STROBO2TORS.recoh_recover_translation_sound

import Aesop
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_coordinate
import Theorems.Thm_Couret_STROBO2TORS_recoh_recovered_sign_bit_sound
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Direct recovery of the unknown two-torsion translation from the signs of
nonzero character readings.  The recovered coordinates are explicit: a
coordinate is zero when the observed and base readings agree, and one
otherwise.  Accepted readings must equal the base reading or its negative.

This module proves both completeness for actual translated observations and
soundness for accepted signs.  It also constructs compatible coordinates for
a separating bank of the minimum size, and instantiates such a bank with the
already proved two-primary character construction.  Three-primary readings
are proved invariant under every recovered two-torsion translation.

Equality of complex values and the inverse coordinate map are noncomputable
here.  No executable arithmetic on cyclotomic representations, running-time
bound, or extraction of a Python implementation is claimed by this module.
-/

namespace Couret.STROBO2TORS







variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable [DecidableEq G]

theorem recoh_recover_translation_sound
    (bank : Fin r → AddChar G ℂ)
    (e : H₂ ≃+ (Fin r → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank i (u : G) = if e u i = 0 then 1 else -1)
    (S : Finset G)
    (hnonzero : ∀ i, recohSupportProbe (bank i) S ≠ 0)
    (obs : Fin r → ℂ)
    (hobs : ∀ i, obs i = recohSupportProbe (bank i) S ∨
      obs i = -recohSupportProbe (bank i) S) :
    ∀ i, recohSupportProbe (bank i)
      (translateSupport S
        (recohRecoverTranslation e (fun j => recohSupportProbe (bank j) S) obs : G)) =
      obs i := by sorry








variable [Fintype G]









end Couret.STROBO2TORS
