-- Prove2me | solution 1 for PGLQuotient.sigmaExp_cons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:34:06.407704+00:00
-- url     : https://prove2.me/submissions/71f6a29a-76c5-454b-a2e4-c6bda78ebb23

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
    sigmaExp (consV a g) = (n + 1) * a + sigmaExp g := by
  unfold sigmaExp
  rw [Finset.sum_range_succ' (fun i => lam (consV a g) 0 - lam (consV a g) i) (n + 1)]
  simp only [Nat.sub_self, Nat.add_zero]
  have hterm : ∀ i ∈ range (n + 1),
      lam (consV a g) 0 - lam (consV a g) (i + 1) = a + (lam g 0 - lam g i) := by
    intro i _
    rw [lam_cons_succ, lam_cons_zero]
    have := lam_antitone g (Nat.zero_le i)
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
