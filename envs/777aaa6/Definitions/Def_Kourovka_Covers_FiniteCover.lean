-- Prove2me | Definitions.Def_Kourovka_Covers_FiniteCover
-- name    : Kourovka_Covers_FiniteCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:42.540584+00:00
-- url     : https://prove2.me/theorems/d1e0a047-75b1-4f7c-969e-ab8e857f86ed
-- title:
--   Finite Cover
-- statement:
--   Definitions and structural lemmas for Finite Cover, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
namespace Kourovka.MetabelianEnumeration.FiniteCover
abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev Polynomial (k : ℕ) := Bool × List (Lattice k × ℤ)
structure Datum (k a : ℕ) where
  /-- The kernel generator assigned to a quotient-generator commutator. -/
  designated : Fin k → Fin k → Fin a
  /-- Ordered signed Laurent relations, imposed at every kernel generator. -/
  polynomials : List (Polynomial k)
def latticeBall (k radius : ℕ) : Finset (Lattice k) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc (-(radius : ℤ)) radius).filter
    fun v => (∑ i, v i ^ 2) < (radius : ℤ) ^ 2
theorem mem_latticeBall {k radius : ℕ} (v : Lattice k) :
    v ∈ latticeBall k radius ↔ (∑ i, v i ^ 2) < (radius : ℤ) ^ 2 := by
  rw [latticeBall, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have hr : (0 : ℤ) ≤ radius := Int.natCast_nonneg radius
    apply Finset.mem_Icc.mpr
    constructor <;> nlinarith
def latticeBallList (k radius : ℕ) : List (Lattice k) :=
  let order : LinearOrder (Lattice k) := LinearOrder.lift' List.ofFn List.ofFn_injective
  letI : LinearOrder (Lattice k) := order
  (latticeBall k radius).sort order.le
theorem mem_latticeBallList {k radius : ℕ} (v : Lattice k) :
    v ∈ latticeBallList k radius ↔ (∑ i, v i ^ 2) < (radius : ℤ) ^ 2 := by
  rw [latticeBallList, Finset.mem_sort, mem_latticeBall]
def rightComm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y
def conjugate {G : Type*} [Group G] (x w : G) : G := w⁻¹ * x * w
def orderedWord {k : ℕ} {G : Type*} [Group G] (t : Fin k → G) (v : Lattice k) : G :=
  (List.ofFn fun i => t i ^ v i).prod
def polynomialWord {k : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (x : G) (p : Polynomial k) : G :=
  (p.2.map fun term => conjugate (x ^ term.2)
    (if p.1 then orderedWord t term.1 else (orderedWord t term.1)⁻¹)).prod
theorem map_rightComm {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (rightComm x y) = rightComm (f x) (f y) := by simp [rightComm]
theorem map_conjugate {G H : Type*} [Group G] [Group H] (f : G →* H) (x w : G) :
    f (conjugate x w) = conjugate (f x) (f w) := by simp [conjugate]
theorem map_orderedWord {k : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t : Fin k → G) (v : Lattice k) :
    f (orderedWord t v) = orderedWord (fun i => f (t i)) v := by
  simp [orderedWord, map_list_prod, List.map_ofFn, Function.comp_def]
theorem map_polynomialWord {k : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t : Fin k → G) (x : G) (p : Polynomial k) :
    f (polynomialWord t x p) = polynomialWord (fun i => f (t i)) (f x) p := by
  simp only [polynomialWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_apply, map_conjugate, map_zpow]
  split <;> simp only [map_orderedWord, map_inv]
def tGenerator (k a : ℕ) (i : Fin k) : FreeGroup (Fin (k + a)) :=
  FreeGroup.of (Fin.castAdd a i)
def aGenerator (k a : ℕ) (i : Fin a) : FreeGroup (Fin (k + a)) :=
  FreeGroup.of (Fin.natAdd k i)
def tRelations {k a : ℕ} (data : Datum k a) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange k).flatMap fun i => ((List.finRange k).filter fun j => i < j).map fun j =>
    rightComm (tGenerator k a i) (tGenerator k a j) *
      (aGenerator k a (data.designated i j))⁻¹
def shortRelations (k a radius : ℕ) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange a).flatMap fun i => (List.finRange a).flatMap fun j =>
    (latticeBallList k radius).map fun v =>
      rightComm (aGenerator k a i) (conjugate (aGenerator k a j)
        (orderedWord (tGenerator k a) v))
def polynomialRelations {k a : ℕ} (data : Datum k a) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange a).flatMap fun i => data.polynomials.map fun p =>
    (aGenerator k a i)⁻¹ * polynomialWord (tGenerator k a) (aGenerator k a i) p
def relators {k a : ℕ} (data : Datum k a) (radius : ℕ) :
    List (FreeGroup (Fin (k + a))) :=
  tRelations data ++ shortRelations k a radius ++ polynomialRelations data
def GroupOf {k a : ℕ} (data : Datum k a) (radius : ℕ) :=
  PresentedGroup (WordCertificates.relSet (relators data radius))
instance {k a : ℕ} (data : Datum k a) (radius : ℕ) : Group (GroupOf data radius) :=
  inferInstanceAs (Group (PresentedGroup (WordCertificates.relSet (relators data radius))))
def generatorAssignment {k a : ℕ} {G : Type*} (t : Fin k → G) (A : Fin a → G) :
    Fin (k + a) → G := Fin.addCases t A
theorem lift_tGenerator {k a : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (A : Fin a → G) (i : Fin k) :
    FreeGroup.lift (generatorAssignment t A) (tGenerator k a i) = t i := by
  simp [generatorAssignment, tGenerator]
theorem lift_aGenerator {k a : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (A : Fin a → G) (i : Fin a) :
    FreeGroup.lift (generatorAssignment t A) (aGenerator k a i) = A i := by
  simp [generatorAssignment, aGenerator]
structure Realizes {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G) : Prop where
  /-- Quotient-generator commutators have their designated kernel values. -/
  t_comm : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j)
  /-- Kernel generators commute at all displacements inside the finite radius. -/
  short_comm : ∀ i j v, (∑ s, v s ^ 2) < (radius : ℤ) ^ 2 →
    rightComm (A i) (conjugate (A j) (orderedWord t v)) = 1
  /-- The signed Laurent identities hold for each kernel generator. -/
  polynomial : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p
theorem realization_relators {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) (r : FreeGroup (Fin (k + a)))
    (hr : r ∈ relators data radius) : FreeGroup.lift (generatorAssignment t A) r = 1 := by
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have hij : i < j := of_decide_eq_true (List.mem_filter.mp hj).2
      simp only [map_mul, map_inv, map_rightComm, lift_tGenerator, lift_aGenerator]
      rw [h.t_comm i j hij]
      exact mul_inv_cancel _
    · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
      simp only [map_rightComm, map_conjugate, map_orderedWord,
        lift_tGenerator, lift_aGenerator]
      exact h.short_comm i j v ((mem_latticeBallList v).mp hv)
  · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [map_mul, map_inv, map_polynomialWord, lift_tGenerator, lift_aGenerator]
    rw [← h.polynomial i p hp]
    exact inv_mul_cancel _
def realizationHom {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) : GroupOf data radius →* G :=
  PresentedGroup.toGroup (f := generatorAssignment t A) (realization_relators data radius t A h)
end Kourovka.MetabelianEnumeration.FiniteCover


