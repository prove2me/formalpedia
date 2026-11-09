-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_primary_translation_recovery
-- name    : Couret.STROBO2TORS.recoh_exists_primary_translation_recovery
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:34.73651+00:00
-- url     : https://prove2.me/theorems/2296a7c3-20b2-4cb2-9811-0c58a9605965
-- title:
--   A primary-two bank recovers every triple translation
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Assume $G$ finite and $|H|=2^r$. There exist characters $\chi_i$ for $i<r$ and an additive equivalence $e:H\cong(\mathbb Z/2\mathbb Z)^r$ such that each $\chi_i(x)$ has two-power order, $\chi_i(u)=(-1)^{e(u)_i}$ for $u\in H$, and for every triple $S$ and every $u\in H$,
--
--   $$\operatorname{Recover}_e((P_{\chi_i}(S))_i,(P_{\chi_i}(S+u))_i)=u.$$
--
--   Recovery sets a bit to zero precisely when its reading is unchanged and then applies $e^{-1}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSignRecovery.lean, lines 233–249; source file SHA-256 9c4330cb72ad0993c6c48361a0b68823a89e5af35e3cfb07799a30c9c651fb1c; theorem Couret.STROBO2TORS.recoh_exists_primary_translation_recovery

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_coordinates_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
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











variable [Fintype G]

theorem recoh_exists_primary_translation_recovery
    (r : ℕ) (hcard : Nat.card H₂ = 2 ^ r) :
    ∃ (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2)),
      (∀ i x, ∃ n : ℕ, (bank i x) ^ (2 ^ n) = 1) ∧
      (∀ (u : H₂) (i : Fin r),
        bank i (u : G) = if e u i = 0 then 1 else -1) ∧
      (∀ (S : Finset G), S.card = 3 → ∀ u : H₂,
        recohRecoverTranslation e
          (fun i => recohSupportProbe (bank i) S)
          (fun i => recohSupportProbe (bank i) (translateSupport S (u : G))) = u) := by sorry


end Couret.STROBO2TORS
