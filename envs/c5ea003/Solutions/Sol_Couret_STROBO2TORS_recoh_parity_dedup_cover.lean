-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_dedup_cover
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:27.840443+00:00
-- url     : https://prove2.me/submissions/cc623b85-af61-4b17-a094-abc24515eb98

import Aesop
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_coverage
import Theorems.Thm_Couret_STROBO2TORS_recoh_anchored_dedup_mem_source
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce

set_option autoImplicit false

/-!
Composition of the parity generator with the historical orbit construction.

The equality below is an equality of finite families of entire H-orbits,
not equality of representatives or their iteration order. Deduplication is
applied to an explicit list enumeration of the parity representatives. The
list and its anchors are inputs with stated representation contracts; no
classical `Finset.toList` is hidden in an executable definition.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



omit [Fintype G] in
/-- Every enumeration with a valid anchor at each support retains coverage
after the explicitly defined right-fold deduplication. -/
theorem p2m_local_recoh_parity_dedup_cover
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (xs : List (Finset G))
    (hxs : xs.toFinset = recohParityRepresentatives U R half)
    (anchor : Finset G → G) (hanchor : ∀ B ∈ xs, anchor B ∈ B) :
    RecohParityCover R (recohAnchoredOrbitDedup anchor xs).toFinset := by
  obtain ⟨hsound, hcomplete⟩ := recoh_parity_representatives_cover U R half hhalf hR
  constructor
  · intro B hB
    have hlist : B ∈ xs := recoh_anchored_dedup_mem_source anchor xs B
      (List.mem_toFinset.mp hB)
    apply hsound B
    rw [← hxs]
    exact List.mem_toFinset.mpr hlist
  · intro S hS hsquare
    obtain ⟨B, hB, hBS⟩ := hcomplete S hS hsquare
    have hlist : B ∈ xs := by
      apply List.mem_toFinset.mp
      rw [hxs]
      exact hB
    obtain ⟨C, hC, hCS⟩ :=
      (recoh_anchored_dedup_coverage anchor xs hanchor S).mpr ⟨B, hlist, hBS⟩
    exact ⟨C, List.mem_toFinset.mpr hC, hCS⟩



section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









end Cyclic

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G)
  (R : G → Nat) (half : G → Option.{p2m_u_0} G),
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{p2m_u_0} G inst half →
    (∀ (z : G),
        @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
      ∀ (xs : List.{p2m_u_0} (Finset.{p2m_u_0} G)),
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@List.toFinset.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) xs)
            (@Couret.STROBO2TORS.recohParityRepresentatives.{p2m_u_0} G inst inst_1 U R half) →
          ∀ (anchor : Finset.{p2m_u_0} G → G),
            (∀ (B : Finset.{p2m_u_0} G),
                @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
                    (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G)) xs B →
                  @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    B (anchor B)) →
              @Couret.STROBO2TORS.RecohParityCover.{p2m_u_0} G inst inst_1 R
                (@List.toFinset.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
                  (@Couret.STROBO2TORS.recohAnchoredOrbitDedup.{p2m_u_0} G inst inst_1 anchor xs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_dedup_cover

