-- Prove2me | Definitions.Def_FSCofinalityCosets20261102
-- name    : FSCofinalityCosets20261102
-- status  : Definition
-- author  : @username
-- created : 2026-11-02T12:39:32.585021+00:00
-- url     : https://prove2.me/theorems/f2ab21bc-0140-4981-8d41-ecd6005dd9d8
-- title:
--   The Polish permutation group and its image-subgroup coset relations
-- statement:
--   The group is the actual group of permutations of the natural numbers. Its standard topology is represented by the permutation and inverse permutation coordinates in two copies of Baire space; Polishness and continuity of the group operations are proved. The sigma algebra is its native Borel sigma algebra. For any subgroup H, p and q are equivalent exactly when q inverse times p belongs to H. For a homomorphism from a subgroup, the image coset relation uses its actual algebraic range. No closedness, normality, or additional topology is imposed on that range by these definitions.
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Section 2.4, permutation groups and cosets; Section 3; Theorem 4.1.

import Definitions.Def_FSCofinalityStructures20261102
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.PiNat

set_option autoImplicit false
noncomputable section
open Set Topology TopologicalSpace Filter

namespace FSCofinality

/-- The full symmetric group of the natural numbers. -/
def PermutationGroup := Equiv.Perm ℕ

instance : Group PermutationGroup := inferInstanceAs (Group (Equiv.Perm ℕ))

/-- A permutation is coded by its function and inverse function. -/
def permutationCoordinates (p : PermutationGroup) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (p.toFun,p.invFun)

/-- The usual permutation topology: pointwise convergence of a permutation
and its inverse, as a subspace of two copies of Baire space. -/
instance : TopologicalSpace PermutationGroup :=
  TopologicalSpace.induced permutationCoordinates inferInstance

instance : MeasurableSpace PermutationGroup := borel PermutationGroup
instance : BorelSpace PermutationGroup := ⟨rfl⟩

theorem continuous_permutationCoordinates : Continuous permutationCoordinates :=
  continuous_induced_dom

theorem permutationCoordinates_injective : Function.Injective permutationCoordinates := by
  intro p q h
  apply Equiv.ext
  intro n
  exact congrFun (congrArg Prod.fst h) n

/-- Evaluation with a varying natural-number index is continuous. -/
theorem continuous_baire_evaluation :
    Continuous (fun p : (ℕ → ℕ) × ℕ => p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have heq : ∀ᶠ q : (ℕ → ℕ) × ℕ in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have h : ContinuousAt (fun q : (ℕ → ℕ) × ℕ => q.1 p.2) p :=
    ((continuous_apply p.2).comp continuous_fst).continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [heq] with q hq
  rw [hq]

def InversePairCondition (p : (ℕ → ℕ) × (ℕ → ℕ)) : Prop :=
  (∀ n, p.1 (p.2 n) = n) ∧ (∀ n, p.2 (p.1 n) = n)

theorem isClosed_inversePairCondition :
    IsClosed {p : (ℕ → ℕ) × (ℕ → ℕ) | InversePairCondition p} := by
  have hf : ∀ n, Continuous (fun p : (ℕ → ℕ) × (ℕ → ℕ) => p.1 (p.2 n)) :=
    fun n => continuous_baire_evaluation.comp
      (continuous_fst.prodMk ((continuous_apply n).comp continuous_snd))
  have hg : ∀ n, Continuous (fun p : (ℕ → ℕ) × (ℕ → ℕ) => p.2 (p.1 n)) :=
    fun n => continuous_baire_evaluation.comp
      (continuous_snd.prodMk ((continuous_apply n).comp continuous_fst))
  have hleft : IsClosed {p : (ℕ → ℕ) × (ℕ → ℕ) | ∀ n, p.1 (p.2 n) = n} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun n => isClosed_eq (hf n) continuous_const)
  have hright : IsClosed {p : (ℕ → ℕ) × (ℕ → ℕ) | ∀ n, p.2 (p.1 n) = n} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun n => isClosed_eq (hg n) continuous_const)
  exact hleft.inter hright

theorem range_permutationCoordinates :
    range permutationCoordinates = {p | InversePairCondition p} := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.apply_symm_apply,q.symm_apply_apply⟩
  · rintro ⟨hf,hg⟩
    exact ⟨⟨p.1,p.2,hg,hf⟩,rfl⟩

instance : PolishSpace PermutationGroup := by
  letI : PolishSpace (ℕ → ℕ) := {
    toSecondCountableTopology := inferInstance
    toIsCompletelyMetrizableSpace := inferInstance }
  apply Topology.IsClosedEmbedding.polishSpace (f := permutationCoordinates)
  exact ⟨permutationCoordinates_injective.isEmbedding_induced,
    range_permutationCoordinates ▸ isClosed_inversePairCondition⟩

theorem continuous_permutation_mul :
    Continuous (fun p : PermutationGroup × PermutationGroup => p.1 * p.2) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro n
    exact continuous_baire_evaluation.comp
      (((continuous_permutationCoordinates.comp continuous_fst).fst).prodMk
        ((continuous_apply n).comp ((continuous_permutationCoordinates.comp continuous_snd).fst)))
  · apply continuous_pi
    intro n
    exact continuous_baire_evaluation.comp
      (((continuous_permutationCoordinates.comp continuous_snd).snd).prodMk
        ((continuous_apply n).comp ((continuous_permutationCoordinates.comp continuous_fst).snd)))

theorem continuous_permutation_inv : Continuous (fun p : PermutationGroup => p⁻¹) := by
  apply continuous_induced_rng.mpr
  exact continuous_permutationCoordinates.snd.prodMk continuous_permutationCoordinates.fst

instance : IsTopologicalGroup PermutationGroup where
  continuous_mul := continuous_permutation_mul
  continuous_inv := continuous_permutation_inv

/-- Left-coset equivalence, with the manuscript's orientation. -/
def CosetRelation (H : Subgroup PermutationGroup) (p q : PermutationGroup) : Prop :=
  q⁻¹ * p ∈ H

def cosetRelation (H : Subgroup PermutationGroup) : CodedRelation where
  Carrier := PermutationGroup
  measurableSpace := inferInstance
  rel := CosetRelation H

/-- Cosets of the actual algebraic image of a subgroup homomorphism. -/
def imageCosetRelation {G : Subgroup PermutationGroup} (π : G →* PermutationGroup) :
    CodedRelation := cosetRelation π.range

end FSCofinality


