-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_MappingComponents
-- name    : AnalyticCombinatorics_Ch2_Mappings_MappingComponents
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:41:40.893102+00:00
-- url     : https://prove2.me/theorems/75dd0cc7-e22c-4248-8372-19a4ab970351
-- title:
--   Cyclic-core component counts and their finite expectation sums
-- statement:
--   A candidate cycle is a nonempty label subset with a single-orbit permutation. A self-map respects it when its restriction agrees with that permutation. Core cycles are compatible candidates in the periodic-point permutation; componentCount is their finite cardinality. Finite correspondences interchange a map with one selected core cycle and a candidate cycle with compatible function values. The expectation formula and its weighted Ramanujan representation are explicit real finite sums.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/MappingComponents.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Components of random mappings

The component count is defined as the number of nonempty single-cycle
restrictions of the permutation induced by a mapping on its periodic core.  A
candidate cycle `C` of a map is counted exactly when the ambient map restricts
to a cyclic permutation on `C`; this is equivalent to being one cycle of the
periodic-core permutation.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-- A nonempty labelled set together with a cyclic permutation on it. -/
abbrev CandidateCycle (n : ℕ) : Type :=
  Sigma fun C : {C : Finset (Fin n) // C.Nonempty} =>
    {σ : Equiv.Perm C.1 // PermSingleCycle σ}

def candidateSupport {n : ℕ} (A : CandidateCycle n) : Finset (Fin n) :=
  A.1.1

def candidatePerm {n : ℕ} (A : CandidateCycle n) : Equiv.Perm (candidateSupport A) :=
  A.2.1

def candidateCard {n : ℕ} (A : CandidateCycle n) : ℕ :=
  (candidateSupport A).card

abbrev MapsRespectingCandidate {n : ℕ} (A : CandidateCycle n) : Type :=
  {f : Fin n → Fin n // ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n)}

/--
The same candidate cycles, but stated on the periodic core: all labels of the
support are periodic, and the restriction of `periodicCorePerm f` to that
support is the candidate cyclic permutation.
-/
abbrev CoreCycleOfMap {n : ℕ} (f : Fin n → Fin n) : Type :=
  {A : CandidateCycle n //
    ∃ hper : ∀ x : candidateSupport A, PeriodicPoint f x.1,
      ∀ x : candidateSupport A,
        ((periodicCorePerm f) ⟨x.1, hper x⟩ : Fin n) = (candidatePerm A x : Fin n)}

@[reducible] def coreCycleOfMapFintype {n : ℕ} (f : Fin n → Fin n) :
    Fintype (CoreCycleOfMap f) := by
  classical
  exact Fintype.ofFinite (CoreCycleOfMap f)

/-- The number of connected components of the functional graph of `f`. -/
def componentCount {n : ℕ} (f : Fin n → Fin n) : ℕ :=
  @Fintype.card (CoreCycleOfMap f) (coreCycleOfMapFintype f)

lemma candidate_iterate {n : ℕ} {f : Fin n → Fin n} {A : CandidateCycle n}
    (hA : ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n))
    (x : candidateSupport A) :
    ∀ m : ℕ, f^[m] x.1 = ((candidatePerm A)^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [candidate_iterate hA x m]
      rw [hA ((candidatePerm A)^[m] x)]
      rw [Function.iterate_succ_apply']

lemma periodicPoint_of_respects_candidate {n : ℕ} {f : Fin n → Fin n}
    {A : CandidateCycle n}
    (hA : ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n))
    (x : candidateSupport A) :
    PeriodicPoint f x.1 := by
  refine ⟨orderOf (candidatePerm A), orderOf_pos (candidatePerm A), ?_⟩
  calc
    f^[orderOf (candidatePerm A)] x.1 =
        ((candidatePerm A)^[orderOf (candidatePerm A)] x : Fin n) := by
          exact candidate_iterate hA x (orderOf (candidatePerm A))
    _ = x.1 := by
          have hpow : (candidatePerm A) ^ orderOf (candidatePerm A) = 1 :=
            pow_orderOf_eq_one (candidatePerm A)
          have hfun : (candidatePerm A)^[orderOf (candidatePerm A)] x = x := by
            rw [← Equiv.Perm.coe_pow, hpow]
            rfl
          exact congrArg Subtype.val hfun

abbrev MapCycleOfMap {n : ℕ} (f : Fin n → Fin n) : Type :=
  {A : CandidateCycle n //
    ∀ x : candidateSupport A, f x.1 = (candidatePerm A x : Fin n)}

/--
Core-cycle candidates are exactly the ambient cyclic restrictions `f|C = σ_C`.
The reverse direction uses the fact that every point of such a restriction is
periodic, so `periodicCorePerm f` is defined on the support.
-/
def coreCycleMapCycleEquiv {n : ℕ} (f : Fin n → Fin n) :
    CoreCycleOfMap f ≃ MapCycleOfMap f where
  toFun A := by
    rcases A with ⟨A, hcore⟩
    let hper := Classical.choose hcore
    let hcore := Classical.choose_spec hcore
    refine ⟨A, ?_⟩
    intro x
    have hx := hcore x
    simpa using hx
  invFun A := by
    rcases A with ⟨A, hA⟩
    let hper : ∀ x : candidateSupport A, PeriodicPoint f x.1 :=
      fun x => periodicPoint_of_respects_candidate hA x
    refine ⟨A, ⟨hper, ?_⟩⟩
    intro x
    simpa using hA x
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

def mapCycleSwapEquiv (n : ℕ) :
    (Sigma fun f : Fin n → Fin n => MapCycleOfMap f) ≃
      (Sigma fun A : CandidateCycle n => MapsRespectingCandidate A) where
  toFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  invFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  left_inv P := by
    rcases P with ⟨f, A, hA⟩
    rfl
  right_inv P := by
    rcases P with ⟨A, f, hA⟩
    rfl

def mapsRespectingCandidateEquiv {n : ℕ} (A : CandidateCycle n) :
    MapsRespectingCandidate A ≃ ({x : Fin n // x ∉ candidateSupport A} → Fin n) where
  toFun F := fun x => F.1 x.1
  invFun g := by
    refine ⟨(fun x =>
      if hx : x ∈ candidateSupport A then
        (candidatePerm A ⟨x, hx⟩ : Fin n)
      else
        g ⟨x, hx⟩), ?_⟩
    intro x
    simp
  left_inv F := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ candidateSupport A
    · simp [hx, F.2 ⟨x, hx⟩]
    · simp [hx]
  right_inv g := by
    funext x
    simp [x.2]

def componentExpectationFormula (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (n.descFactorial k : ℝ) / ((k : ℝ) * (n : ℝ)^k)

def weightedRamanujanComponents (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ramanujanQTerm n i / ((i + 1 : ℕ) : ℝ)

end

end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS


