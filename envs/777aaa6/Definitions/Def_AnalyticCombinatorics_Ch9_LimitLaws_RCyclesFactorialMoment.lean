-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesFactorialMoment
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_RCyclesFactorialMoment
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:13:38.301505+00:00
-- url     : https://prove2.me/theorems/e23a7ee3-6240-4bf9-8d91-5f09b884c351
-- title:
--   Cycle incidences and complement-permutation equivalences
-- statement:
--   Finite types represent cycles of a prescribed length, cycle factors of a fixed permutation, permutations containing a distinguished cycle and permutations disjoint from it. Finite structures and explicit equivalences count the same incidence first by the permutation and then by the cycle, including analogues on arbitrary finite types.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/RCyclesFactorialMoment.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Factorial moments for fixed-length cycles

This file records unconditional finite-average identities for the genuine
`rCycleCount` random variable from `RCyclesPoisson.lean`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

namespace FM

/-- A nontrivial cycle on `Fin n` with support of cardinality `r`. -/
abbrev CyclesOfLength (n r : ℕ) : Type :=
  {c : Equiv.Perm (Fin n) // c.IsCycle ∧ c.support.card = r}

/-- The `r`-cycle factors of a fixed permutation. -/
abbrev CyclesOfLengthOfPerm (n r : ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  {c : σ.cycleFactorsFinset // (c : Equiv.Perm (Fin n)).support.card = r}

/-- Permutations that contain a fixed cycle as one of their cycle factors. -/
abbrev PermContainingCycle {n r : ℕ} (c : CyclesOfLength n r) : Type :=
  {σ : Equiv.Perm (Fin n) // (c : Equiv.Perm (Fin n)) ∈ σ.cycleFactorsFinset}

/-- Permutations disjoint from a fixed cycle. -/
abbrev PermDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) : Type :=
  {τ : Equiv.Perm (Fin n) // Equiv.Perm.Disjoint τ (c : Equiv.Perm (Fin n))}

instance instFintypeCyclesOfLength (n r : ℕ) : Fintype (CyclesOfLength n r) := by
  classical
  unfold CyclesOfLength
  infer_instance

instance instFintypeCyclesOfLengthOfPerm (n r : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CyclesOfLengthOfPerm n r σ) := by
  classical
  unfold CyclesOfLengthOfPerm
  infer_instance

instance instFintypePermContainingCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype (PermContainingCycle c) := by
  classical
  unfold PermContainingCycle
  infer_instance

instance instFintypePermDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype (PermDisjointCycle c) := by
  classical
  unfold PermDisjointCycle
  infer_instance

/-- Removing a contained cycle leaves a permutation disjoint from that cycle. -/
def permContainingCycleEquivDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    PermContainingCycle c ≃ PermDisjointCycle c where
  toFun σ :=
    ⟨σ.1 * (c : Equiv.Perm (Fin n))⁻¹,
      Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset σ.2⟩
  invFun τ :=
    ⟨τ.1 * (c : Equiv.Perm (Fin n)), by
      have hc_mem :
          (c : Equiv.Perm (Fin n)) ∈
            (c : Equiv.Perm (Fin n)).cycleFactorsFinset := by
        rw [(c.prop.1).cycleFactorsFinset_eq_singleton]
        simp
      have hcycles :
          (τ.1 * (c : Equiv.Perm (Fin n))).cycleFactorsFinset =
            τ.1.cycleFactorsFinset ∪ (c : Equiv.Perm (Fin n)).cycleFactorsFinset :=
        τ.2.cycleFactorsFinset_mul_eq_union
      rw [hcycles]
      exact Finset.mem_union_right _ hc_mem⟩
  left_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv τ := by
    apply Subtype.ext
    simp [mul_assoc]

def permDisjointCycleEquivComplement {n r : ℕ} (c : CyclesOfLength n r) :
    Equiv.Perm {x : Fin n // x ∉ (c : Equiv.Perm (Fin n)).support} ≃
      PermDisjointCycle c :=
  (Equiv.Perm.subtypeEquivSubtypePerm
      (fun x : Fin n => x ∉ (c : Equiv.Perm (Fin n)).support)).trans
    { toFun := fun τ =>
        ⟨τ.1, by
          intro x
          by_cases hx : x ∈ (c : Equiv.Perm (Fin n)).support
          · exact Or.inl (τ.2 x (by simpa using hx))
          · exact Or.inr (Equiv.Perm.notMem_support.mp hx)⟩
      invFun := fun τ =>
        ⟨τ.1, by
          intro x hx
          rcases τ.2 x with hτ | hc
          · exact hτ
          · have hxmem : x ∈ (c : Equiv.Perm (Fin n)).support := by simpa using hx
            exact False.elim ((Equiv.Perm.mem_support.mp hxmem) hc)⟩
      left_inv := by
        rintro ⟨τ, hτ⟩
        rfl
      right_inv := by
        rintro ⟨τ, hτ⟩
        rfl }

/-- Count the same incidence relation first by ambient permutation. -/
abbrev CycleByPerm (n r : ℕ) : Type :=
  Σ σ : Equiv.Perm (Fin n), CyclesOfLengthOfPerm n r σ

/-- Count the same incidence relation first by the distinguished cycle. -/
abbrev CycleByCycle (n r : ℕ) : Type :=
  Σ c : CyclesOfLength n r, PermContainingCycle c

def cycleByPermEquivCycleByCycle (n r : ℕ) :
    CycleByPerm n r ≃ CycleByCycle n r where
  toFun x :=
    ⟨⟨x.2.1, (Equiv.Perm.mem_cycleFactorsFinset_iff.mp x.2.1.prop).1, x.2.2⟩,
      ⟨x.1, x.2.1.prop⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨⟨x.1.1, x.2.2⟩, x.1.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, c, hcard⟩
    rfl
  right_inv := by
    rintro ⟨c, σ, hmem⟩
    rfl

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A nontrivial cycle of length `r` in an arbitrary finite type. -/
abbrev CyclesOfLengthIn (r : ℕ) : Type u :=
  {c : Equiv.Perm α // c.IsCycle ∧ c.support.card = r}

/-- The `r`-cycle factors of a fixed permutation of an arbitrary finite type. -/
abbrev CyclesOfLengthOfPermIn (r : ℕ) (σ : Equiv.Perm α) : Type u :=
  {c : σ.cycleFactorsFinset // (c : Equiv.Perm α).support.card = r}

/-- Permutations that contain a fixed cycle as one of their cycle factors. -/
abbrev PermContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) : Type u :=
  {σ : Equiv.Perm α // (c : Equiv.Perm α) ∈ σ.cycleFactorsFinset}

/-- Permutations disjoint from a fixed cycle. -/
abbrev PermDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) : Type u :=
  {τ : Equiv.Perm α // Equiv.Perm.Disjoint τ (c : Equiv.Perm α)}

instance instFintypeCyclesOfLengthIn (r : ℕ) :
    Fintype (CyclesOfLengthIn (α := α) r) := by
  classical
  unfold CyclesOfLengthIn
  infer_instance

instance instFintypeCyclesOfLengthOfPermIn (r : ℕ) (σ : Equiv.Perm α) :
    Fintype (CyclesOfLengthOfPermIn (α := α) r σ) := by
  classical
  unfold CyclesOfLengthOfPermIn
  infer_instance

instance instFintypePermContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype (PermContainingCycleIn c) := by
  classical
  unfold PermContainingCycleIn
  infer_instance

instance instFintypePermDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype (PermDisjointCycleIn c) := by
  classical
  unfold PermDisjointCycleIn
  infer_instance

def permContainingCycleEquivDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    PermContainingCycleIn c ≃ PermDisjointCycleIn c where
  toFun σ :=
    ⟨σ.1 * (c : Equiv.Perm α)⁻¹,
      Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset σ.2⟩
  invFun τ :=
    ⟨τ.1 * (c : Equiv.Perm α), by
      have hc_mem : (c : Equiv.Perm α) ∈ (c : Equiv.Perm α).cycleFactorsFinset := by
        rw [(c.prop.1).cycleFactorsFinset_eq_singleton]
        simp
      have hcycles :
          (τ.1 * (c : Equiv.Perm α)).cycleFactorsFinset =
            τ.1.cycleFactorsFinset ∪ (c : Equiv.Perm α).cycleFactorsFinset :=
        τ.2.cycleFactorsFinset_mul_eq_union
      rw [hcycles]
      exact Finset.mem_union_right _ hc_mem⟩
  left_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv τ := by
    apply Subtype.ext
    simp [mul_assoc]

def permDisjointCycleEquivComplementIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} ≃ PermDisjointCycleIn c :=
  (Equiv.Perm.subtypeEquivSubtypePerm
      (fun x : α => x ∉ (c : Equiv.Perm α).support)).trans
    { toFun := fun τ =>
        ⟨τ.1, by
          intro x
          by_cases hx : x ∈ (c : Equiv.Perm α).support
          · exact Or.inl (τ.2 x (by simpa using hx))
          · exact Or.inr (Equiv.Perm.notMem_support.mp hx)⟩
      invFun := fun τ =>
        ⟨τ.1, by
          intro x hx
          rcases τ.2 x with hτ | hc
          · exact hτ
          · have hxmem : x ∈ (c : Equiv.Perm α).support := by simpa using hx
            exact False.elim ((Equiv.Perm.mem_support.mp hxmem) hc)⟩
      left_inv := by
        rintro ⟨τ, hτ⟩
        rfl
      right_inv := by
        rintro ⟨τ, hτ⟩
        rfl }

def permComplementEquivContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} ≃ PermContainingCycleIn c :=
  (permDisjointCycleEquivComplementIn c).trans
    (permContainingCycleEquivDisjointCycleIn c).symm

abbrev CycleByPermIn (r : ℕ) : Type u :=
  Σ σ : Equiv.Perm α, CyclesOfLengthOfPermIn (α := α) r σ

abbrev CycleByCycleIn (r : ℕ) : Type u :=
  Σ c : CyclesOfLengthIn (α := α) r, PermContainingCycleIn c

def cycleByPermEquivCycleByCycleIn (r : ℕ) :
    CycleByPermIn (α := α) r ≃ CycleByCycleIn (α := α) r where
  toFun x :=
    ⟨⟨x.2.1, (Equiv.Perm.mem_cycleFactorsFinset_iff.mp x.2.1.prop).1, x.2.2⟩,
      ⟨x.1, x.2.1.prop⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨⟨x.1.1, x.2.2⟩, x.1.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, c, hcard⟩
    rfl
  right_inv := by
    rintro ⟨c, σ, hmem⟩
    rfl

end GeneralFinite

end FM

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


