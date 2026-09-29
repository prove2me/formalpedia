-- Prove2me | solution 1 for Bridges.AlgebraEMLComputation.IterationSystem.kleene_chain_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:19.046654+00:00
-- url     : https://prove2.me/submissions/06b963a6-7666-47bc-9f42-e5ea79b28e5a

-- Sol generated from Bridges/ClosureFixedPointCircuitDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureFixedPointCircuitDuality
/-
# Closure Fixed-Point Circuit Duality

## Algebraic-Computational Duality via Idempotent Iteration and Certified Minimal Feedback

This file establishes a duality between finite monotone closure-controlled iteration
systems and finite feedback circuits computing least fixed points. The key results are:

1. **Bounded Kleene stabilization**: Monotone inflationary maps on finite-height closure
   systems stabilize in bounded steps, with the stabilization point being the least
   fixed point above the closure of the starting element.

2. **Realization**: Every such system admits a finite monotone feedback circuit realization.

3. **Minimality via iteration indistinguishability**: The quotient by the natural
   observational equivalence yields a canonical minimal realization, unique up to
   isomorphism.

4. **Capacity = convergence depth**: The algebraic closure capacity invariant equals
   the worst-case convergence depth of the minimal circuit.

## Bridges

- **Idempotent algebra ↔ Order theory**: Join-semilattice = idempotent commutative monoid
- **Closure dynamics ↔ Monotone computation**: Closure-stable iteration = feedback circuit
- **Algebraic invariants ↔ Computational complexity**: Closure height = convergence depth
- **Quotient algebra ↔ Automata minimization**: Iteration indistinguishability = Myhill-Nerode
-/


open Function Set Classical

noncomputable section

open Bridges.AlgebraEMLComputation

/-! ## §1. Closure Operators on Partial Orders -/





/-! ## §2. Idempotent Iteration System -/


variable {α : Type*} [PartialOrder α] [Fintype α]

open IterationSystem


/-
The Kleene chain is monotone increasing.
-/

/-
If the chain stabilizes at step `n`, it stays stable forever.
-/

/-
A stabilized value is a fixed point of `F`.
-/

/-! ## §3. Finite Height and Bounded Stabilization -/

/-
**Core Stabilization Theorem**: On a finite type, the Kleene chain of any monotone
    inflationary map stabilizes within `Fintype.card α` steps.
-/

/-
Stabilization at the card bound for all starting points.
-/

/-! ## §4. Least Fixed Point Characterization -/

/-
The iterate `F^[N] (cl x)` is a fixed point of `F` when N ≥ card.
-/

/-
The iterate `F^[N] (cl x)` is above `cl x`.
-/

/-
**Least Fixed Point Theorem**: `F^[N] (cl x)` is the least fixed point of `F`
    above `cl x`, when `N` is at least `Fintype.card α`.
-/

/-! ## §5. Feedback Circuit Model -/



open FeedbackCircuit



/-! ## §6. Realization Theorem -/

/-
**Realization Theorem**: Every iteration system on a finite type admits a feedback
    circuit realization that computes the same Kleene iteration.
-/

/-! ## §7. Iteration Indistinguishability -/


open IterationIndistinguishable

variable (S : IterationSystem α)







/-! ## §8. F Respects Iteration Indistinguishability -/

/-
`F` preserves iteration indistinguishability.
-/

/-! ## §9. Minimal Realization via Quotient -/



/-
**Minimality Theorem**: The quotient identifies exactly the
    iteration-indistinguishable elements.
-/

/-! ## §10. Capacity = Convergence Depth -/


/-
**Capacity-Depth Equality**: The algebraic capacity (cardinality) bounds
    convergence depth, and this bound is tight.
-/

/-! ## §11. Join-Semilattice and Idempotent Addition -/

/-
The natural order from idempotent addition: `x ⊔ y = y ↔ x ≤ y`.
-/

/-
Idempotent self-join: `x ⊔ x = x`.
-/

/-! ## §12. Compositional Properties -/

/-
Iterates compose: `F^[m] (F^[n] x) = F^[m + n] x`.
-/

/-
The closure commutes with all iterates of F.
-/

/-! ## §13. Summary

The package of theorems:

1. `kleene_chain_stabilizes` — Bounded stabilization on finite types
2. `kleene_iterate_eq_lfp` — Least fixed point characterization
3. `feedbackCircuit_of_iterationSystem` — Realization theorem
4. `quotient_is_minimal_realization` — Minimality via iteration indistinguishability
5. `capacity_bounds_convergence` — Capacity bounds convergence
6. `cl_iterate_comm` — Closure-iteration commutativity
7. `F_respects_iterationIndistinguishable` — F descends to quotient

Together, these establish that finite closure-controlled iteration systems are
equivalent to finite monotone feedback circuits, with canonical minimal
realizations recoverable from the algebraic closure profile.
-/


open Bridges.AlgebraEMLComputation.IterationSystem in
theorem solution(S : IterationSystem α) :
    ∀ x : α, ∃ n : ℕ, n ≤ Fintype.card α ∧
      S.F^[n] x = S.F^[n + 1] x := by
        intro x
        by_contra h_contra
        push_neg at h_contra
        have h_seq : ∀ n ≤ Fintype.card α, S.F^[n] x < S.F^[n+1] x := by
          intro n hn
          have h_le : S.F^[n] x ≤ S.F^[n+1] x := by
            simpa only [ Function.iterate_succ_apply' ] using S.F_inflationary _
          exact lt_of_le_of_ne h_le (h_contra n hn);
        -- By induction, we can show that $S.F^[n] x$ is strictly increasing for $n \leq Fintype.card α$.
        have h_inc : StrictMonoOn (fun n => S.F^[n] x) (Finset.range (Fintype.card α + 1)) := by
          intro n hn m hm hnm; induction hnm <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
          exact lt_trans ( by solve_by_elim [ Nat.le_of_lt ] ) ( h_seq _ hm.le );
        exact absurd ( Finset.card_le_univ ( Finset.image ( fun n => S.F^[n] x ) ( Finset.range ( Fintype.card α + 1 ) ) ) ) ( by rw [ Finset.card_image_of_injOn fun n hn m hm hnm => h_inc.eq_iff_eq ( by aesop ) ( by aesop ) |>.1 hnm ] ; simp +decide )
