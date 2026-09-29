-- Prove2me | solution 1 for ClosureNucleusDuality.nucleus_fixed_fragment_characterization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:18:07.352331+00:00
-- url     : https://prove2.me/submissions/af8e3598-0298-4545-90dc-e7589f8e6af7

-- Sol generated from Bridges/ClosureNucleusDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureNucleusDuality
/-
# Closure–Nucleus Spectral Duality via Idempotent Semimodules

This file formalizes a finite duality theorem at the interface of closure systems,
idempotent algebra, and algebraic logic. The core result shows that closure-theoretic
data equipped with a logical nucleus can be represented exactly by evaluation on
join-prime spectral points, and that this representation supports certified
reconstruction of closure operators and sound-and-complete Kripke-style semantics.

## Main Results

* `closure_subset_of_closed_superset` — Closure containment from superset closure.
* `implication_valid_iff_all_prime_points` — Completeness: x ∈ cl(A) ↔ all primes
  containing A contain x.
* `closure_equals_sInter_of_prime_points` — Closure reconstruction from prime
  intersection.
* `spectral_eval_injective` — Injectivity of the spectral evaluation map under
  separation.
* `finite_closure_nucleus_spectral_embedding` — Bijection between closed sets
  and spectral observables.
* `certified_closure_reconstruction` — Certified recovery of the closure operator
  from spectral data.
* `implication_semantics_complete` — Sound-and-complete finite Kripke semantics.
* `implicational_basis_reconstruction` — Finite implicational basis generation.
* `nucleus_fixed_fragment_characterization` — Reconstruction of the nucleus-fixed
  fragment from nucleus-stable primes.

Keywords: spectral duality, closure systems, nuclei, idempotent semimodules,
Horn logic, implicational bases, Kripke semantics, formal concept analysis,
certified reconstruction, finite Stone duality.
-/


open Set Function

open ClosureNucleusDuality

/-! ## Section 1: Core Definitions -/





/-! ## Section 2: Basic Properties of Closure Operators -/

variable {α : Type*}

/-- The image of a closure operator is always closed. -/
theorem cl_is_closed (cl : Set α → Set α) (hcl : IsClosureOperator cl) (s : Set α) :
    IsClosed cl (cl s) :=
  hcl.idempotent s

/-- If s ⊆ t and t is closed, then cl(s) ⊆ t. -/
theorem closure_subset_of_closed_superset (cl : Set α → Set α) (hcl : IsClosureOperator cl)
    (s t : Set α) (ht : IsClosed cl t) (hst : s ⊆ t) : cl s ⊆ t := by
  have h1 : cl s ⊆ cl t := hcl.mono hst
  rw [show cl t = t from ht] at h1
  exact h1


/-! ## Section 3: Separation and Spectral Completeness -/




/-! ## Section 4: Spectral Evaluation Map -/



/-! ## Section 5: Finite Spectral Embedding and Duality -/

-- open removed: section is not a namespace
noncomputable section
variable [Fintype α] [DecidableEq α]



/-! ## Section 6: Certified Theory Reconstruction -/


/-! ## Section 7: Kripke Semantics -/



/-! ## Section 8: Implicational Basis Reconstruction -/




/-! ## Section 9: Nucleus-Fixed Fragment Characterization -/


/-! ## Section 10: Spectral Reconstruction Bridge -/


/-! ## Section 11: Full Duality — Closed Sets ≅ Downward-Closed Observables

In the finite setting, the spectral evaluation gives not just an embedding
but a full bijection between closed sets and realizable observables. Combined
with the reconstruction theorems, this gives the complete finite closure–nucleus
spectral duality. -/


/-! ## Section 12: Certified Theory Reconstruction (Combined) -/



open ClosureNucleusDuality in
theorem solution    (C : FiniteClosureNucleus α)
    (hsep_nuc : ∀ (s : Set α) (x : α),
      IsClosed C.cl s → C.nuc s = s → x ∉ s →
      ∃ p, JoinPrimeClosed C.cl C.nuc p ∧ C.nuc p = p ∧ s ⊆ p ∧ x ∉ p)
    (A : Set α) :
    C.nuc (C.cl A) =
      ⋂₀ {p | JoinPrimeClosed C.cl C.nuc p ∧ C.nuc p = p ∧ A ⊆ p} := by
  ext x; simp only [mem_sInter, mem_setOf_eq]; constructor
  · intro hx p ⟨hp, hnp, hAp⟩
    have hclAp : C.cl A ⊆ p :=
      closure_subset_of_closed_superset C.cl C.isClosure A p hp.closed hAp
    have : C.nuc (C.cl A) ⊆ C.nuc p := C.nuc_mono hclAp
    rw [hnp] at this
    exact this hx
  · intro hall
    by_contra hx
    have hclosed : IsClosed C.cl (C.nuc (C.cl A)) :=
      C.nuc_closed (C.cl A) (cl_is_closed C.cl C.isClosure A)
    have hstable : C.nuc (C.nuc (C.cl A)) = C.nuc (C.cl A) := C.nuc_idem (C.cl A)
    obtain ⟨p, hp, hnp, hsp, hxp⟩ := hsep_nuc (C.nuc (C.cl A)) x hclosed hstable hx
    have hAp : A ⊆ p :=
      Subset.trans (Subset.trans (C.isClosure.extensive A)
        (C.nuc_extensive_on_closed (C.cl A) (cl_is_closed C.cl C.isClosure A))) hsp
    exact hxp (hall p ⟨hp, hnp, hAp⟩)
