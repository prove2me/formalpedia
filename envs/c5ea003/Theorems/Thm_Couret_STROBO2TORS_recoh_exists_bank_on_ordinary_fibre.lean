-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_ordinary_fibre
-- name    : Couret.STROBO2TORS.recoh_exists_bank_on_ordinary_fibre
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:57.092963+00:00
-- url     : https://prove2.me/theorems/5252d7b6-561f-4ae0-bfc9-b43f79fe7284
-- title:
--   An ordinary fibre admits a bank of its two-torsion rank
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Assume $G$ finite and $|H|=2^r$. If $|S|=3$ and $|F(S)|=|H|$, there is a bank of $r$ complex additive characters with
--
--   $$T\longmapsto(P_{\chi_i}(T))_{i<r}\quad\text{injective on }F(S).$$
--
--   The bank may be selected for this fibre.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreUpper.lean, lines 104–122; source file SHA-256 682ad74687cb91c6b5c8d4f92be42d438a63b3a643e0e0c7a5093423d4d3efdc; theorem Couret.STROBO2TORS.recoh_exists_bank_on_ordinary_fibre

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_bank_injective_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
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

theorem recoh_exists_bank_on_ordinary_fibre
    (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (S : Finset G) (hS : S.card = 3)
    (hordinary : (squareFibre S).card = (twoTorsion : Finset G).card) :
    ∃ bank : Fin r → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S) := by sorry








end Couret.STROBO2TORS
