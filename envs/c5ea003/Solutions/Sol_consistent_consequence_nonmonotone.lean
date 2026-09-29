-- Prove2me | solution 1 for consistent_consequence_nonmonotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:50:32.206083+00:00
-- url     : https://prove2.me/submissions/e2918c06-fb70-4396-9a82-9da42c76d6a8

-- Sol generated from Logic/PosetTheory/BelnapBilattice.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_BelnapBilattice
/-
  Belnap's FOUR₂ as a Distributive Bilattice

  We formalize Belnap's four-valued logic FOUR₂ and prove it carries the structure of
  a *distributive bilattice*: two bounded distributive lattice orderings (truth and
  knowledge) on the same four-element set, connected by a De Morgan negation that is
  an antitone involution in the truth ordering and a monotone lattice homomorphism in
  the knowledge ordering. We prove this negation is NOT a Boolean complement, which is
  the algebraic root of paraconsistency — the failure of "explosion" (ex falso quodlibet).

  ## Main Results

  1. `Belnap.instDistribLattice` — Truth ordering forms a bounded distributive lattice
  2. `Belnap.bneg_deMorgan_inf` / `bneg_deMorgan_sup` — De Morgan laws for Belnap negation
  3. `Belnap.bneg_not_complement` — Belnap negation violates non-contradiction (paraconsistency)
  4. `Belnap.explosion_fails` — Ex falso quodlibet fails
  5. `Belnap.kLE_distribLattice_axioms` — Knowledge ordering satisfies distributive lattice axioms
  6. `Belnap.bneg_antitone` — Negation is antitone in truth ordering
  7. `Belnap.bneg_kLE_monotone` — Negation is monotone in knowledge ordering
  8. `Belnap.bneg_k_homomorphism` — Negation is a knowledge-lattice homomorphism
  9. `consistent_consequence_nonmonotone` — Consistent credulous consequence is non-monotone

  ## References

  - Belnap, N. (1977). "A useful four-valued logic"
  - Fitting, M. (2002). "Bilattices and the Semantics of Logic Programming"
  - Arieli, O. & Avron, A. (1996). "Reasoning with logical bilattices"
-/

set_option autoImplicit false

/-! ## The Belnap Type -/


open Belnap


/-! ## Belnap Negation -/


/-! ## Truth Ordering

The truth ordering on FOUR₂ forms a diamond (M₂) lattice:
```
       T (top)
      / \
     B   N
      \ /
       F (bottom)
```
B and N are incomparable; F is the least element, T is the greatest.
-/



/-! ## Truth Ordering: DistribLattice Instance -/




instance : Top Belnap where top := T


-- !-- The truth ordering on FOUR₂ is the diamond lattice M₂, which is a bounded
-- distributive lattice. All axioms are verified by exhaustive case analysis
-- over the 4-element type. -- !--

/-! ## Negation Properties in Truth Ordering -/


-- !-- De Morgan's laws hold for Belnap negation with respect to the truth ordering.
-- This is proved by exhaustive case analysis on the 4×4 cases. -- !--



-- !-- The central paraconsistency result: Belnap negation is NOT a lattice complement.
-- In a Boolean algebra, a ⊓ compl a = ⊥ for all a. Here, B ⊓ bneg B = B ⊓ B = B ≠ F = ⊥.
-- This is the algebraic root of paraconsistency. -- !--




/-! ## Knowledge Ordering

The knowledge ordering on FOUR₂ also forms a diamond lattice, but rotated 90°:
```
       B (top — maximal information)
      / \
     T   F
      \ /
       N (bottom — no information)
```
T and F are incomparable in the knowledge ordering.
-/





/-! ## Knowledge Ordering: Distributive Lattice Axioms -/

-- !-- The knowledge ordering also forms a bounded distributive lattice, with N as bottom
-- and B as top. This gives FOUR₂ its bilattice structure: two independent lattice
-- orderings on the same set. Proved by exhaustive case analysis. -- !--













/-! ## Bilattice Structure: Negation and Knowledge Ordering -/

-- !-- Negation is MONOTONE in the knowledge ordering (unlike truth ordering where it's
-- antitone). This is the key bilattice interaction: negation reverses one ordering
-- but preserves the other. Moreover, negation is a lattice HOMOMORPHISM for the
-- knowledge ordering (preserving both meet and join). -- !--




/-! ## Independence of the Two Orderings -/


/-! ## Interlacing: Truth Operations Distribute over Knowledge Operations -/

-- !-- FOUR₂ is an INTERLACED bilattice: the truth meet and join are monotone with
-- respect to the knowledge ordering. This means truth operations preserve
-- information content. Proved by 64-case exhaustion. -- !--




/-! ## Non-Monotonicity of Consistent Credulous Consequence -/


variable {α : Type}




-- !-- Consistent credulous consequence is non-monotone: adding information to a
-- knowledge base can invalidate previously derivable conclusions. The witness
-- uses Unit (single variable): kb₁ = {((), T)} has a consistent model (v _ = T),
-- but kb₂ = {((), T), ((), F)} is unsatisfiable (v () = T and v () = F
-- simultaneously is impossible). -- !--



-- open removed: section is not a namespace
theorem solution:
    ∃ (kb₁ kb₂ : Set (Unit × Belnap)) (x : Unit),
      kb₁ ⊆ kb₂ ∧ ConsistentCredulousTruth kb₁ x ∧ ¬ConsistentCredulousTruth kb₂ x := by
  refine ⟨{((), Belnap.T)}, {((), Belnap.T), ((), Belnap.F)}, (), ?_, ?_, ?_⟩
  · -- kb₁ ⊆ kb₂
    intro p hp; simp_all
  · -- kb₁ has a consistent satisfying valuation
    refine ⟨fun _ => Belnap.T, fun _ h => Belnap.noConfusion h, ?_, rfl⟩
    intro p hp; simp only [Set.mem_singleton_iff] at hp; rw [hp]
  · -- kb₂ is unsatisfiable: v () = T and v () = F is impossible
    intro ⟨v, _, hsat, _⟩
    have h1 := hsat ((), Belnap.T) (by simp)
    have h2 := hsat ((), Belnap.F) (by simp)
    simp at h1 h2
    rw [h1] at h2; exact Belnap.noConfusion h2
