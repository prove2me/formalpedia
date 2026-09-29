-- Prove2me | solution 1 for Bridges.AlgebraEMLTropical.ClosureRateDistortionDuality.capacity_singleton_determines
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:20.693409+00:00
-- url     : https://prove2.me/submissions/d07e346c-0a9b-45d9-8614-88947dccecbe

-- Sol generated from Bridges/ClosureRateDistortionDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureRateDistortionDuality
/-
# Tropical Rate–Distortion Duality via Idempotent Information Semimodules

This file formalizes a duality between finite closure-information systems and
tropical rate–distortion profiles, yielding certified minimal quantizer
reconstruction from closure capacity data.

## Main results

- `closureCapacity_class_invariant` — Capacity is constant on closure classes.
- `closure_to_tropical_profile` — Unique tropical profile from closure capacity.
- `rdProfile_top_eq_zero` — RD profile at ⊤ is 0.
- `quantizerEquiv_distortion_eq` — Equivalent quantizers have same distortion.
- `closure_rd_duality_summary` — Main duality theorem.
- `tropical_semimodule_laws` — Min-plus semimodule axioms.
- `tropicalLegendre_antitone` — Tropical Legendre transform is antitone.
- `closure_morphism_contracts` — Data processing inequality.
- `ultraDist_triangle` — Ultrametric triangle inequality.

## Bridges

- **Closure Theory ↔ Lossy Compression**: Closure atoms = optimal codebook cells.
- **Tropical Algebra ↔ Information Theory**: Min-plus operations = rate–distortion.
- **Lattice Theory ↔ Quantization**: Join-irreducible elements = irreducible cells.
-/


open Set Classical

noncomputable section

open Bridges.AlgebraEMLTropical.ClosureRateDistortionDuality

/-! ## §1. Closure Operator -/




/-! ## §2. Closure Capacity -/




/-! ## §3. Separation Axiom -/


/-! ## §4. Closure Equivalence -/




/-! ## §5. Quantizer -/




/-! ## §6. Distortion -/


/-! ## §7. Quantizer Equivalence -/



/-
Equivalent quantizers have the same distortion.
-/


/-! ## §8. Tropical Min-Plus Algebra -/













/-! ## §9. Tropical Distortion Vectors -/






/-! ## §10. Closure-Induced Distortion -/



/-! ## §11. Rate–Distortion Profile -/



/-
The RD profile is antitone: higher distortion ⟹ fewer generators exceed it.
-/


/-! ## §12. Capacity Union Bound -/



/-! ## §13. Tropical Legendre Transform -/



/-! ## §14. Tropical Pairing -/



/-! ## §15. Generator Theorem -/



/-! ## §16. Forward Direction of Duality -/


/-! ## §17. Cell Capacity Bound -/


/-! ## §18. Closure Atom Structure -/



/-! ## §19. Feasible Rates -/



/-! ## §20. Concrete Examples -/







/-! ## §21. Ultrametric Information Distance -/



/-
The ultrametric strong triangle inequality.
-/

/-! ## §22. Capacity Bounded by Closure Containment -/


/-! ## §23. Capacity Table and Optimal Cell Count -/




/-
Optimal cell count is antitone.
-/

/-! ## §24. Main Duality Summary -/


/-! ## §25. Information Contraction (Data Processing Inequality) -/

/-
**Theorem**: Closure morphisms contract information.
A closure morphism `f : α → β` (with `f '' (clα s) ⊆ clβ (f '' s)`) induces
a pullback capacity that is no larger than the original.
-/





/-
**Theorem**: Two capacities agreeing on singletons agree on all sets
(via closure invariance).
-/


open Bridges.AlgebraEMLTropical.ClosureRateDistortionDuality in
theorem solution{α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (v w : ClCap α cl)
    (h : ∀ a : α, v.val {a} = w.val {a}) :
    ∀ s : Set α, v.val (cl s) = w.val (cl s) := by
  cases' v with v hv;
  cases' w with w hw;
  intro s;
  -- By definition of $v$ and $w$, we know that $v(s) \leq \max_{a \in s} v(\{a\})$ and $w(s) \leq \max_{a \in s} w(\{a\})$.
  have h_le_max : v s ≤ sSup (Set.image (fun a => v {a}) s) ∧ w s ≤ sSup (Set.image (fun a => w {a}) s) := by
    have h_le_max : ∀ (s : Finset α), v (s : Set α) ≤ sSup (Set.image (fun a => v {a}) (s : Set α)) ∧ w (s : Set α) ≤ sSup (Set.image (fun a => w {a}) (s : Set α)) := by
      intro s;
      induction' s using Finset.induction with a s ha ih;
      · aesop;
      · simp_all +decide [ Set.image_insert_eq ];
        have := ‹∀ s t : Set α, v ( cl ( s ∪ t ) ) ≤ max ( v s ) ( v t ) › { a } s; have := ‹∀ s t : Set α, w ( cl ( s ∪ t ) ) ≤ max ( w s ) ( w t ) › { a } s; simp_all +decide [ Set.union_comm ] ;
        exact ⟨ Or.imp id ( fun h => h.trans ih.1 ) ‹v ( insert a ↑s ) ≤ w { a } ∨ v ( insert a ↑s ) ≤ v ↑s›, Or.imp id ( fun h => h.trans ih.2 ) ‹w ( insert a ↑s ) ≤ w { a } ∨ w ( insert a ↑s ) ≤ w ↑s› ⟩;
    convert h_le_max ( s.toFinset ) using 1 <;> simp +decide [ Set.ext_iff ];
  by_cases hs : s.Nonempty <;> simp_all +decide [ Set.Nonempty ];
  · -- Since $s$ is nonempty, there exists some $a \in s$ such that $w \{a\} = \sup_{a \in s} w \{a\}$.
    obtain ⟨a, ha⟩ : ∃ a ∈ s, w {a} = sSup (Set.image (fun a => w {a}) s) := by
      have h_finite : Set.Finite (Set.image (fun a => w {a}) s) := by
        exact Set.toFinite _;
      exact ( IsCompact.sSup_mem h_finite.isCompact <| Set.Nonempty.image _ hs );
    have h_le_max : v s ≥ v {a} ∧ w s ≥ w {a} := by
      exact ⟨ by apply_assumption; exact Set.singleton_subset_iff.mpr ha.1, by apply_assumption; exact Set.singleton_subset_iff.mpr ha.1 ⟩;
    grind;
  · rw [ show s = ∅ by ext x; simp +decide [ hs ] ] ; aesop
