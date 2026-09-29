-- Prove2me | solution 1 for Erdos180.symplecticIncidence_card_by_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:37:31.873022+00:00
-- url     : https://prove2.me/submissions/6ac5ada8-0d48-49b2-8904-b7a97f2f69ab

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticPointOrthogonal_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointOrthogonal K p) = 3 := by
  change Module.finrank K
    ((standardSymplecticBilin K).orthogonal p.1) = 3
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K), p.2]
  simp [SymplecticVector]

lemma symplecticPointQuotient_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointQuotient K p) = 2 := by
  change Module.finrank K
    (↥(SymplecticPointOrthogonal K p) ⧸
      SymplecticPointRadical K p) = 2
  have h := Submodule.finrank_quotient_add_finrank
    (SymplecticPointRadical K p)
  rw [symplecticPointRadical_finrank K p,
    symplecticPointOrthogonal_finrank K p] at h
  omega

lemma symplecticLinesOnPoint_card [Finite K]
    (p : SymplecticPoint K) :
    Nat.card (SymplecticLinesOnPoint K p) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticLinesOnPointEquiv K p)]
  exact Projectivization.card_of_finrank_two K
    (SymplecticPointQuotient K p)
    (symplecticPointQuotient_finrank K p)

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ p : SymplecticPoint K,
          SymplecticLinesOnPoint K p) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaPoints K)
    _ = ∑ p : SymplecticPoint K,
          Nat.card (SymplecticLinesOnPoint K p) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
      simp_rw [symplecticLinesOnPoint_card]
      simp [Nat.card_eq_fintype_card]
