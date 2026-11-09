-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeCollisionDarts_eq_fibre_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:36.012269+00:00
-- url     : https://prove2.me/submissions/85d42557-5a60-4eb5-b274-0abd4611cc94

import Aesop
import Definitions.Def_Couret_Strobo2TorsFibreMoment_8377f9a18ab8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Mathlib.Data.Sym.Card

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
M002.4: a combinatorial, rather than numerical, bridge between the second
binomial moment of the nonempty zero-free square fibres and the three
symmetric-difference collision edge counts.

The common object is an ordered pair of distinct supports in a single
restricted fibre. Each undirected graph edge has exactly two orientations.
No translation orbit is divided out, and no division of any numerical
closed-form count is used.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



/-- The restricted square fibre of a zero-free triple belongs to the
existing collection of nonempty, distinct restricted fibres. -/
private theorem zeroFreeFibre_of_support (S : Finset G)
    (hS : S.card = 3) (h0 : 0 ∉ S) :
    withoutZero (squareFibre S) ∈
      (zeroFreeFullFibres : Finset (Finset (Finset G))) := by
  change withoutZero (squareFibre S) ∈
    (nonemptyFullFibres (G := G)).image (withoutZero (G := G))
  apply Finset.mem_image.mpr
  refine ⟨squareFibre S, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨S, (mem_tripleSupports S).mpr hS, rfl⟩
  · exact ⟨S, Finset.mem_filter.mpr
      ⟨(mem_squareFibre S S).mpr ⟨hS, fun _ => rfl⟩, h0⟩⟩

/-- A support in a surviving restricted fibre uniquely determines the
whole restricted fibre, even in small groups. -/
private theorem zeroFreeFibre_eq_of_mem
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hSF : S ∈ F) :
    S.card = 3 ∧ 0 ∉ S ∧ F = withoutZero (squareFibre S) := by
  change F ∈ (nonemptyFullFibres (G := G)).image (withoutZero (G := G)) at hF
  obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
  obtain ⟨hKall, _⟩ := Finset.mem_filter.mp hK
  have hSrest : S ∈ withoutZero K := by
    rw [hKF]
    exact hSF
  have hSK : S ∈ K := (Finset.mem_filter.mp hSrest).1
  have hS0 : 0 ∉ S := (Finset.mem_filter.mp hSrest).2
  obtain ⟨U, hU, hUK⟩ := Finset.mem_image.mp hKall
  have hSU : S ∈ squareFibre U := by
    rw [hUK]
    exact hSK
  have hS3 : S.card = 3 := ((mem_squareFibre U S).mp hSU).1
  have hKS : squareFibre S = K :=
    allSquareFibres_squareFibre_member K hKall S hSK
  refine ⟨hS3, hS0, ?_⟩
  simpa only [hKS] using hKF.symm

/-- Exact membership equivalence: two supports lie in one existing
restricted fibre iff they have the required square and avoid zero. -/
private theorem commonZeroFreeFibre_iff (S T : Finset G) :
    (∃ F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))),
      S ∈ F ∧ T ∈ F) ↔
    S.card = 3 ∧ T.card = 3 ∧ 0 ∉ S ∧ 0 ∉ T ∧
      (∀ z : G, orderedSquare S z = orderedSquare T z) := by
  constructor
  · rintro ⟨F, hF, hSF, hTF⟩
    obtain ⟨hS3, hS0, hFS⟩ := zeroFreeFibre_eq_of_mem F hF S hSF
    obtain ⟨hT3, hT0, _⟩ := zeroFreeFibre_eq_of_mem F hF T hTF
    have hTrest : T ∈ withoutZero (squareFibre S) := by
      rw [← hFS]
      exact hTF
    have hsq := ((mem_squareFibre S T).mp (Finset.mem_filter.mp hTrest).1).2
    exact ⟨hS3, hT3, hS0, hT0, hsq⟩
  · rintro ⟨hS3, hT3, hS0, hT0, hsq⟩
    refine ⟨withoutZero (squareFibre S), zeroFreeFibre_of_support S hS3 hS0,
      ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨(mem_squareFibre S S).mpr ⟨hS3, fun _ => rfl⟩, hS0⟩
    · exact Finset.mem_filter.mpr
        ⟨(mem_squareFibre S T).mpr ⟨hT3, hsq⟩, hT0⟩

/-- The fibre-indexed oriented pairs are exactly the collision darts.
This is an equality of finsets, not just their cardinalities. -/
theorem p2m_local_zeroFreeCollisionDarts_eq_fibre_biUnion :
    (zeroFreeCollisionDarts (G := G)) =
      (zeroFreeFullFibres : Finset (Finset (Finset G))).biUnion
        (fun F => F.offDiag) := by
  classical
  ext p
  simp only [zeroFreeCollisionDarts, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, Finset.mem_offDiag]
  constructor
  · rintro ⟨hS3, hT3, hST, hsq, hS0, hT0⟩
    obtain ⟨F, hF, hSF, hTF⟩ :=
      (commonZeroFreeFibre_iff p.1 p.2).mpr ⟨hS3, hT3, hS0, hT0, hsq⟩
    exact ⟨F, hF, hSF, hTF, hST⟩
  · rintro ⟨F, hF, hSF, hTF, hST⟩
    obtain ⟨hS3, hT3, hS0, hT0, hsq⟩ :=
      (commonZeroFreeFibre_iff p.1 p.2).mp ⟨F, hF, hSF, hTF⟩
    exact ⟨hS3, hT3, hST, hsq, hS0, hT0⟩



















end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2)
    (@Finset.biUnion.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (fun a b =>
        @instDecidableEqProd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) fun F =>
      @Finset.offDiag.{p2m_u_0} (Finset.{p2m_u_0} G) F) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeCollisionDarts_eq_fibre_biUnion

