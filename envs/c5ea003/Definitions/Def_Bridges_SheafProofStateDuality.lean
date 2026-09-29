-- Prove2me | Definitions.Def_Bridges_SheafProofStateDuality
-- name    : Bridges_SheafProofStateDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:19.667334+00:00
-- url     : https://prove2.me/theorems/67cca77d-e5a3-493a-b277-2b6aace65f95
-- title:
--   Aether Catalog definitions — Bridges_SheafProofStateDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SheafProofStateDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SheafProofStateDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Sheaf–Proof-State Duality via Finite Cohomological Obstruction Theory

A finite combinatorial theorem package: for proof-state dependency complexes,
failure of a globally coherent proof policy is *exactly* first cohomology,
and every nonzero obstruction yields an extractable minimal inconsistent cycle.

## Main Results

* `coboundary_is_cocycle` — every coboundary is a cocycle (δ² = 0)
* `global_section_iff_H1_trivial` — global extendability ↔ H¹ = 0
* `exists_inclusion_minimal_nontrivial_support` — minimal obstruction extraction
* `nontrivial_cocycle_lower_bounds_instability` — H¹ ≠ 0 ⟹ instability ≥ 1
* `finite_separation_holds` — finite separation for global sections
* `cohomological_vanishing_minimal_realization` — learnability/minimality duality
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

namespace SheafProofStateDuality

/-! ## §1. Proof Dependency Complex -/

/-- A finite proof-state dependency complex. -/
structure ProofDependencyComplex (ι : Type*) where
  edge : ι → ι → Prop
  edge_irrefl : ∀ i, ¬ edge i i
  edge_symm : ∀ i j, edge i j → edge j i
  triangle : ι → ι → ι → Prop
  triangle_edges : ∀ i j k, triangle i j k → edge i j ∧ edge j k ∧ edge i k

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-! ## §2. Cochains and Coboundary -/

/-- The coboundary map δ : (ι → M) → (ι × ι → M), defined as (δf)(i,j) = f(j) - f(i). -/
def coboundary (f : ι → M) : ι × ι → M :=
  fun p => f p.2 - f p.1

/-! ## §3. Cocycles, Coboundaries, H¹ -/

/-- A 1-cochain `z` is a cocycle if `z(i,j) + z(j,k) = z(i,k)` on all triangles. -/
def IsCocycle (K : ProofDependencyComplex ι) (z : ι × ι → M) : Prop :=
  ∀ i j k, K.triangle i j k → z (i, j) + z (j, k) = z (i, k)

/-- A 1-cochain is a coboundary if `z = δf` for some `f`. -/
def IsCoboundary (_K : ProofDependencyComplex ι) (z : ι × ι → M) : Prop :=
  ∃ f : ι → M, coboundary f = z

/-- H¹ trivial: every cocycle is a coboundary. -/
def H1Trivial (K : ProofDependencyComplex ι) (M : Type*) [AddCommGroup M] : Prop :=
  ∀ z : ι × ι → M, IsCocycle K z → IsCoboundary K z

/-- H¹ nontrivial: some cocycle is not a coboundary. -/
def H1Nontrivial (K : ProofDependencyComplex ι) (M : Type*) [AddCommGroup M] : Prop :=
  ∃ z : ι × ι → M, IsCocycle K z ∧ ¬ IsCoboundary K z

/-- Global extendability: every cocycle is a coboundary. -/
def GlobalExtendability (K : ProofDependencyComplex ι) (M : Type*) [AddCommGroup M] : Prop :=
  ∀ z : ι × ι → M, IsCocycle K z → IsCoboundary K z

/-! ## §4. Core Theorems -/

/-
**δ² = 0**: Every coboundary is a cocycle.
    Proof: `(f(j)-f(i)) + (f(k)-f(j)) = f(k)-f(i)`.
-/

/-
**Global extendability ↔ H¹ trivial** (definitional equivalence).
-/

/-
**H¹ nontrivial ↔ ¬ H¹ trivial.**
-/

/-! ## §5. Cohomology Classes -/

/-- Two cochains are cohomologous if their difference is a coboundary. -/
def SameCohomologyClass (K : ProofDependencyComplex ι)
    (z₁ z₂ : ι × ι → M) : Prop :=
  IsCoboundary K (z₁ - z₂)



/-! ## §6. Support and Minimal Obstruction Extraction -/

/-- Support of a 1-cochain restricted to edges. -/
def cochainSupport (K : ProofDependencyComplex ι) [∀ i j, Decidable (K.edge i j)]
    (z : ι × ι → M) : Finset (ι × ι) :=
  (Finset.univ.filter (fun p : ι × ι => K.edge p.1 p.2)).filter (fun e => z e ≠ 0)

/-- Inclusion-minimal nontrivial support. -/
def InclusionMinimalNontrivialSupport (K : ProofDependencyComplex ι)
    [∀ i j, Decidable (K.edge i j)] (z : ι × ι → M) : Prop :=
  ¬ IsCoboundary K z ∧
  ∀ z' : ι × ι → M,
    ¬ IsCoboundary K z' →
    SameCohomologyClass K z z' →
    cochainSupport K z' ⊆ cochainSupport K z →
    cochainSupport K z = cochainSupport K z'

/-
**Certified Minimal Counterexample Reconstruction.**
    Any nontrivial cocycle has a cohomologous representative with
    inclusion-minimal nontrivial support. Follows by well-founded
    descent on the cardinality of support (finite).
-/

/-! ## §7. Instability Lower Bound -/

/-- Disagreement count: number of pairs where `δf ≠ z`. -/
def PredictorDisagreementCount
    (f : ι → M) (z : ι × ι → M) : ℕ :=
  (Finset.univ.filter (fun p : ι × ι => coboundary f p ≠ z p)).card

/-- Instability lower bound: every predictor disagrees on ≥ n pairs. -/
def InstabilityLowerBound
    (z : ι × ι → M) (n : ℕ) : Prop :=
  ∀ f : ι → M, n ≤ PredictorDisagreementCount f z

/-
**Nontrivial cocycle forces positive instability.**
    If `z` is not a coboundary, every predictor disagrees on ≥ 1 pair.
-/

/-
**H¹ nontrivial ⟹ positive instability bound.**
-/

/-! ## §8. Global Sections Subgroup -/


/-- The global sections form an additive subgroup. -/
def GlobalSectionsSubgroup (K : ProofDependencyComplex ι) :
    AddSubgroup (ι → M) where
  carrier := { f | coboundary (M := M) f = 0 }
  zero_mem' := by ext p; simp [coboundary]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    ext p; simp only [coboundary, Pi.zero_apply]
    have ha' := congr_fun ha p; have hb' := congr_fun hb p
    simp only [coboundary, Pi.zero_apply] at ha' hb'
    simp only [Pi.add_apply]
    have h1 : a p.2 - a p.1 = 0 := ha'
    have h2 : b p.2 - b p.1 = 0 := hb'
    rw [sub_eq_zero] at h1 h2 ⊢; rw [h1, h2]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    ext p; simp only [coboundary, Pi.zero_apply]
    have ha' := congr_fun ha p
    simp only [coboundary, Pi.zero_apply] at ha'
    simp only [Pi.neg_apply]
    rw [sub_eq_zero] at ha' ⊢; rw [ha']

/-
Membership ↔ zero coboundary.
-/

/-
When `M` is finite, global sections form a finite set.
-/
theorem global_sections_finite (K : ProofDependencyComplex ι) [Fintype M] :
    Set.Finite (GlobalSectionsSubgroup K (M := M)).carrier := by
  exact Set.toFinite _

/-! ## §9. Learnability / Minimality Duality -/

/-- Minimal architecture size: cardinality of the global sections set. -/
def MinimalArchitectureSize (K : ProofDependencyComplex ι) [Fintype M] : ℕ :=
  (global_sections_finite K (M := M)).toFinset.card

/-- Finite separation: distinct global sections differ at some vertex. -/
def FiniteSeparationHypothesis (K : ProofDependencyComplex ι) : Prop :=
  ∀ f g : ι → M,
    f ∈ (GlobalSectionsSubgroup K).carrier →
    g ∈ (GlobalSectionsSubgroup K).carrier →
    f ≠ g → ∃ i : ι, f i ≠ g i

/-
Finite separation always holds for functions with decidable eq.
-/

/-
**Learnability/Minimality Duality.** The minimal architecture equals
    the global sections cardinality. Combined with H¹ = 0, this reduces
    proof-predictor realizability to a finite generation problem, which
    the catalog theorem `finite_separation_semimodule_realization_minimal`
    identifies with minimal generators.
-/

/-! ## §10. Obstruction Characterization -/

/-
Zero coboundary ↔ global section membership.
-/

/-
Extendability ↔ coboundary (definitional).
-/

end SheafProofStateDuality


