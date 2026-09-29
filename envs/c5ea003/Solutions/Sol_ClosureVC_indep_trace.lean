-- Prove2me | solution 1 for ClosureVC.indep_trace
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:52.01273+00:00
-- url     : https://prove2.me/submissions/d5f15f4a-be84-49e0-924f-5d62a39c286b

-- Sol generated from Bridges/ClosureVCDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureVCDuality

/-!
# Closure–VC Duality: Algebraic Foundations of Learnability

This file establishes a fundamental duality between closure operators on finite sets
and the VC dimension / sample compression theory from statistical learning.

## Main Results

1. **`closure_vc_duality`**: For any closure operator on a finite type, the VC dimension
   of the concept class of closed sets equals the maximum closure rank:
   `VCDimBound (closedConceptClass cl) d ↔ ∀ A : Finset X, ClosureRankBound cl A d`

2. **`certified_closure_reconstruction`**: The closure operator provides a canonical
   reconstruction function: `cl(positives)` is the unique minimal closed set containing
   the positive examples.

3. **`closure_compression_scheme`**: Bounded closure rank yields a certified sample
   compression scheme of the same size.

## Mathematical Significance

This theorem reveals that VC dimension — the central combinatorial invariant of
learnability — is equivalent to closure rank — the algebraic invariant measuring
generator complexity in the lattice of closed sets. The equivalence is exact, not
up to constants, and holds for all finite closure systems.
-/

open Finset Set Function

noncomputable section

open ClosureVC

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## §1. Closure Operator Definitions -/




/-! ## §2. Shattering and VC Dimension -/



/-! ## §3. Closure Rank -/



/-! ## §4. Fundamental Lemmas -/


omit [Fintype X] [DecidableEq X] in
/-- If `S ⊆ H` and `H` is cl-closed, then `cl S ⊆ H`. -/
theorem cl_le_closed (cl : Set X → Set X) (hcl : IsClosureOp cl)
    (S H : Set X) (hSH : S ⊆ H) (hH : ClClosed cl H) : cl S ⊆ H :=
  hH ▸ hcl.mono hSH

/-
Key: if A is closure-independent, then `cl(T) ∩ A = T` for every `T ⊆ A`.
-/



/-! ## §5. Minimum Generator Existence -/

/-
Every finite set has a minimum-cardinality generating subset.
-/

/-! ## §6. Main Duality Theorem -/


/-
**Backward**: bounded VC dimension → bounded closure rank.
-/



/-! ## §7. Certified Closure Reconstruction -/




/-! ## §8. Closure-Based Sample Compression -/




/-
**Closure Compression**: bounded closure rank → compression scheme.
-/




open ClosureVC in
theorem solution(cl : Set X → Set X) (hcl : IsClosureOp cl)
    (A : Finset X) (hind : ClosureIndep cl A) :
    ∀ T : Finset X, T ⊆ A → ∀ x : X, x ∈ A → (x ∈ cl (↑T : Set X) ↔ x ∈ T) := by
  intro T hT x hx;
  constructor;
  · contrapose!;
    intro hxT hxcl
    have h_subset : T ⊆ A.erase x := by
      exact fun y hy => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hxT hy ) ( hT hy )
    have h_closure : cl (↑T : Set X) ⊆ cl (↑(A.erase x) : Set X) := by
      exact hcl.mono ( Finset.coe_subset.mpr h_subset )
    have h_eq : cl (↑(A.erase x) : Set X) = cl (↑A : Set X) := by
      refine' le_antisymm _ _;
      · exact hcl.mono ( Finset.coe_subset.mpr ( Finset.erase_subset _ _ ) );
      · have h_closure : cl (↑A : Set X) ⊆ cl (↑(A.erase x) : Set X) := by
          have h_subset : ↑A ⊆ cl (↑(A.erase x) : Set X) := by
            intro y hy; by_cases hyx : y = x <;> simp_all +decide [ Set.subset_def ] ;
            exact hcl.extensive _ ( by aesop )
          apply cl_le_closed;
          · exact hcl;
          · exact h_subset;
          · exact hcl.idem _;
        exact h_closure
    have h_contra : A ⊆ A.erase x := by
      exact hind _ ( Finset.erase_subset _ _ ) h_eq
    exact absurd ( Finset.mem_erase.mp ( h_contra hx ) ) ( by simp +decide );
  · exact fun h => hcl.extensive _ h
