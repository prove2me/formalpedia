-- Prove2me | solution 1 for PGLQuotient.firstBlockSize_cons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:34:00.618273+00:00
-- url     : https://prove2.me/submissions/183c0f56-2522-4fb4-9371-12b848c41938

-- Sol generated from Algebra/PGLQuotient/TwistedWeight.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_gapAt_consV_succ
import Theorems.Thm_PGLQuotient_gapAt_consV_zero
import Theorems.Thm_PGLQuotient_lam_antitone

/-!
# The twisted vertex mass and its row-peeling recursion

To compute the vertex volume of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))`
in arbitrary rank we enlarge the vertex mass `1/|Aut λ|` to a two-parameter family.

For a vertex `λ` of rank `d` (in the gap model of `Algebra.PGLQuotient.VertexModel`) put

* `sigmaExp λ = ∑_i (λ_0 - λ_i)` — the "top-row defect";
* `firstBlockSize λ = #{ i : λ_i = λ_0 }` — the size of the block of maximal entries;
* `blockProdShift q j λ = ∏_i (1 - q^{-(r_i + j·[λ_i = λ_0])})` — the Levi factor with the
  ranks in the top block shifted by `j`;
* `twWeight q c j λ = (q^{dim End + c·σ + j·m} · blockProdShift q j λ)⁻¹`.

For `c = j = 0` this is exactly the vertex mass: `twWeight q 0 0 = vertexWeight q`
(`twWeight_zero_zero`).

The point of the two extra parameters is that the family is *stable under peeling off the top
row of `λ`*: writing a rank-`(n+2)` vertex as `Fin.cons a λ'` with `a = λ_0 - λ_1 ≥ 0` the gap
between the first row and the rest, one gets (`twWeight_cons_zero`, `twWeight_cons_succ`)

`twWeight q c j (cons 0 λ') = K · twWeight q (c+1) (j+1) λ'`,
`twWeight q c j (cons (a+1) λ') = K · q^{-(n+1)(c+1)(a+1)} · twWeight q (c+1) 0 λ'`,

with `K = (q^{n+2+j}(1 - q^{-(1+j)}))⁻¹`.  This is the recursion which, summed over all
vertices, produces the closed product form of the vertex volume.
-/

open PGLQuotient

open Finset

variable {d : ℕ}






variable {q : ℝ}










variable {n : ℕ}


/-- Peeling the first index off a filtered cardinality over a range. -/
lemma card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ((range (N + 1)).filter p).card
      = ((range N).filter (fun i => p (i + 1))).card + (if p 0 then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']



lemma lam_cons_succ (a : ℕ) (g : Vertex (n + 1)) (i : ℕ) :
    lam (consV a g) (i + 1) = lam g i := by
  unfold lam
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show n + 2 - 1 - (i + 1) = n + 1 - 1 - i by omega]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show i + 1 + t = (i + t) + 1 by omega, gapAt_consV_succ]

lemma lam_cons_zero (a : ℕ) (g : Vertex (n + 1)) :
    lam (consV a g) 0 = a + lam g 0 := by
  unfold lam
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel]
  rw [show n + 2 - 1 = n + 1 from rfl,
    Finset.sum_range_succ' (fun t => gapAt (consV a g) t) n, gapAt_consV_zero,
    Finset.sum_congr rfl (fun t _ => gapAt_consV_succ a g t), Nat.add_comm]








variable {q : ℝ}





open PGLQuotient in
theorem solution(a : ℕ) (g : Vertex (n + 1)) :
    firstBlockSize (consV a g)
      = (if a = 0 then firstBlockSize g else 0) + 1 := by
  unfold firstBlockSize
  rw [card_filter_range_succ (fun i => lam (consV a g) i = lam (consV a g) 0) (n + 1), if_pos rfl]
  congr 1
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    congr 1
    refine Finset.filter_congr (fun i _ => ?_)
    rw [lam_cons_succ, lam_cons_zero, Nat.zero_add]
  · rw [if_neg ha]
    have : (range (n + 1)).filter (fun i => lam (consV a g) (i + 1) = lam (consV a g) 0) = ∅ := by
      refine Finset.filter_false_of_mem (fun i _ => ?_)
      rw [lam_cons_succ, lam_cons_zero]
      have := lam_antitone g (Nat.zero_le i)
      omega
    rw [this, Finset.card_empty]
