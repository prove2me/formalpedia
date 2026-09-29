-- Prove2me | solution 1 for PGLQuotient.tailInjection_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:28:15.180521+00:00
-- url     : https://prove2.me/submissions/d63f29f2-646a-4206-9a5d-8a4fcd7098b7

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# The sharp cusp-tail estimate of order `T^{-d}`

For the standard arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`,
with the normalised lattice-minima height `α` of `Algebra.PGLQuotient.VertexModel`, we prove
the two-sided cusp-tail estimate

`c · T^{-d} ≤ mass {α > T} ≤ C · T^{-d}`   for all `T ≥ 1`.

The upper bound is the delicate half: the naive estimate coming from the integrability
threshold only gives `T^{-r}` for every `r < d`.  The sharp exponent is obtained by
*fibering the gap lattice over the height exponent*: the linear form
`N(g) = ∑_k (d-1-k) g_k = d log_q α` determines the first gap coordinate `g_0` once the
remaining coordinates are known, and the residual exponent `R(g) = ∑_k k(d-1-k) g_k` does not
involve `g_0` at all.  Hence `∑_{N(g) = n} q^{-R(g)}` is bounded uniformly in `n`, and
summing the resulting geometric series in `n` produces the exact exponent `T^{-d}`.

The lower bound comes from a single vertex on the cusp ray `λ = (n, 0, …, 0)`.
-/

open PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}



/-! ### The fibering majorant -/






/-- Splitting off the zeroth gap coordinate from the height exponent. -/
lemma heightExp_split (g : Vertex d) (h0 : 0 < d - 1) :
    heightExp g = (d - 1) * g ⟨0, h0⟩ + ∑ k ∈ Finset.Ico 1 (d - 1), (d - 1 - k) * gapAt g k := by
  unfold heightExp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h0]
  congr 1
  · have : gapAt g 0 = g ⟨0, h0⟩ := by simp [gapAt, h0]
    rw [this]
    simp



/-! ### From the fibered bound to the sharp `T^{-d}` cusp tail -/






open PGLQuotient in
theorem solution(n₀ : ℕ) (h0 : 0 < d - 1) :
    Function.Injective (fun g : {g : Vertex d // n₀ < heightExp g} =>
      ((heightExp (g : Vertex d) - (n₀ + 1) : ℕ),
        Function.update (g : Vertex d) ⟨0, h0⟩ 0)) := by
  rintro ⟨g, hg⟩ ⟨g', hg'⟩ hEq
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨h1, h2⟩ := hEq
  have hne : ∀ k : Fin (d - 1), k ≠ ⟨0, h0⟩ → g k = g' k := by
    intro k hk
    have := congrFun h2 k
    rwa [Function.update_of_ne hk, Function.update_of_ne hk] at this
  have hgap : ∀ k ∈ Finset.Ico 1 (d - 1),
      (d - 1 - k) * gapAt g k = (d - 1 - k) * gapAt g' k := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hk1 : k < d - 1 := hk.2
    have e1 : gapAt g k = g ⟨k, hk1⟩ := by simp [gapAt, hk1]
    have e2 : gapAt g' k = g' ⟨k, hk1⟩ := by simp [gapAt, hk1]
    rw [e1, e2]
    congr 1
    exact hne ⟨k, hk1⟩ (by
      intro hc
      have : k = 0 := by simpa using congrArg (Fin.val) hc
      omega)
  have hheight : heightExp g = heightExp g' := by omega
  have hsplit := heightExp_split g h0
  have hsplit' := heightExp_split g' h0
  rw [Finset.sum_congr rfl hgap] at hsplit
  have hval : (d - 1) * g ⟨0, h0⟩ = (d - 1) * g' ⟨0, h0⟩ := by omega
  have h0' : g ⟨0, h0⟩ = g' ⟨0, h0⟩ := by
    have : 0 < d - 1 := h0
    exact Nat.eq_of_mul_eq_mul_left this hval
  have hgg : g = g' := by
    funext k
    by_cases hk : k = ⟨0, h0⟩
    · subst hk; exact h0'
    · exact hne k hk
  exact Subtype.ext hgg
