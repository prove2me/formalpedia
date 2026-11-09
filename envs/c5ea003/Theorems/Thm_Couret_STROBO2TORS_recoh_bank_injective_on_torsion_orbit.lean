-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_bank_injective_on_torsion_orbit
-- name    : Couret.STROBO2TORS.recoh_bank_injective_on_torsion_orbit
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:51.456594+00:00
-- url     : https://prove2.me/theorems/6f3dbdf8-6102-4f36-9989-9f27b46e809b
-- title:
--   A separating nonzero character bank identifies two-torsion translates
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a finite support $S$, and $P_\chi(S)=\sum_{s\in S}\chi(s)$ its complex character reading. Write $O(S)=\{S+u:2u=0\}$. Assume $G$ is finite, let $\chi_i$ be a character bank indexed by any type $I$, and let $S$ be a finite support. Suppose every $P_{\chi_i}(S)\ne0$ and every $u$ with $2u=0$ and $\chi_i(u)=1$ for all $i$ is zero. Then
--
--   $$T,U\in O(S),\ [\forall i,\ P_{\chi_i}(T)=P_{\chi_i}(U)]\Longrightarrow T=U.$$
--
--   The support need not be a triple.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreUpper.lean, lines 18–49; source file SHA-256 682ad74687cb91c6b5c8d4f92be42d438a63b3a643e0e0c7a5093423d4d3efdc; theorem Couret.STROBO2TORS.recoh_bank_injective_on_torsion_orbit

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Finite.Card

set_option autoImplicit false

/-!
Character banks chosen after the labelled ordered square has been observed.
The bank may depend on the complete square fibre, but is fixed on that fibre.
The ordinary fibre needs the two-torsion rank many character slots.  An
exceptional fibre needs at most one additional character slot, independently
of the three-torsion rank of the ambient finite abelian group.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_bank_injective_on_torsion_orbit
    {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G)
    (hnonzero : ∀ i : I, recohSupportProbe (bank i) S ≠ 0)
    (hsep : ∀ u : G, u + u = 0 → (∀ i : I, bank i u = 1) → u = 0) :
    Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (torsionOrbit S) := by sorry
















end Couret.STROBO2TORS
