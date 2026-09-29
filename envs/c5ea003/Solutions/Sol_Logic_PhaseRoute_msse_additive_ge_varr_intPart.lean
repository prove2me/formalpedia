-- Prove2me | solution 1 for Logic.PhaseRoute.msse_additive_ge_varr_intPart
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:07:00.980761+00:00
-- url     : https://prove2.me/submissions/b7ef7d48-8525-460b-9f37-5507ac853080

/-
# `Logic.PhaseRoute.msse_additive_ge_varr_intPart`
Target `57b851a0` (WA,WA,WA,CE). Gift: SAFE. Binders from its own WA:
[Fintype α] [Fintype β] [Nonempty α] [Nonempty β], no DecidableEq.

SPLICED, not imported — preflight forbids local `Theorems/` imports, so the three lemmas this rests
on are re-derived inline: `hrow` (= ba7daedb), `hcol` (= b519e970) and `hcross` (= c72e84ea).

DECOMPOSITION. `addPart f - additive u v` is itself additive, with w a = rowMean f a - u a and
z b = colMean f b - avg f - v b, so `f - additive u v = intPart f + additive w z`. Expanding gives
avg(I²) + 2·avg(I·G) + avg(G²); the cross term vanishes because intPart has zero marginals, and
avg (intPart f) = 0 makes varr (intPart f) = avg(I²). Dropping avg(G²) ≥ 0 finishes.

NOTE: `field_simp` CLOSES `hmsse`; the trailing `ring` errored with "No goals to be solved".
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
import Definitions.Def_Logic_PhaseRouteANOVA

set_option maxHeartbeats 800000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α × β → ℝ) (u : α → ℝ) (v : β → ℝ) :
    varr (intPart f) ≤ msse f (additive u v) := by
  have hA : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hT : (∑ b : β, ∑ a' : α, f (a', b)) = ∑ x : α × β, f x := by
    rw [Fintype.sum_prod_type]; exact Finset.sum_comm
  have hT2 : (∑ a : α, ∑ b' : β, f (a, b')) = ∑ x : α × β, f x := (Fintype.sum_prod_type f).symm
  have key : ∀ (a : α) (b : β), intPart f (a, b)
      = f (a, b) - (∑ b' : β, f (a, b')) / (Fintype.card β : ℝ)
        - (∑ a' : α, f (a', b)) / (Fintype.card α : ℝ)
        + (∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
    intro a b
    simp only [intPart, addPart, additive, rowMean, colMean, avg, Fintype.card_prod, Nat.cast_mul]
    ring
  -- ba7daedb, spliced
  have hrow : ∀ a : α, (∑ b : β, intPart f (a, b)) = 0 := by
    intro a
    have s2 : (∑ _b : β, (∑ b' : β, f (a, b')) / (Fintype.card β : ℝ))
        = (Fintype.card β : ℝ) * ((∑ b' : β, f (a, b')) / (Fintype.card β : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have s3 : (∑ b : β, (∑ a' : α, f (a', b)) / (Fintype.card α : ℝ))
        = (∑ x : α × β, f x) / (Fintype.card α : ℝ) := by rw [← Finset.sum_div, hT]
    have s4 : (∑ _b : β, (∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))
        = (Fintype.card β : ℝ)
            * ((∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun b _ => key a b), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, s2, s3, s4]
    field_simp
    ring
  -- b519e970, spliced
  have hcol : ∀ b : β, (∑ a : α, intPart f (a, b)) = 0 := by
    intro b
    have s2 : (∑ a : α, (∑ b' : β, f (a, b')) / (Fintype.card β : ℝ))
        = (∑ x : α × β, f x) / (Fintype.card β : ℝ) := by rw [← Finset.sum_div, hT2]
    have s3 : (∑ _a : α, (∑ a' : α, f (a', b)) / (Fintype.card α : ℝ))
        = (Fintype.card α : ℝ) * ((∑ a' : α, f (a', b)) / (Fintype.card α : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have s4 : (∑ _a : α, (∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))
        = (Fintype.card α : ℝ)
            * ((∑ x : α × β, f x) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun a _ => key a b), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, s2, s3, s4]
    field_simp
    ring
  set w : α → ℝ := fun a => rowMean f a - u a with hwdef
  set z : β → ℝ := fun b => colMean f b - avg f - v b with hzdef
  have hsplit : ∀ x : α × β, f x - additive u v x = intPart f x + additive w z x := by
    intro x
    simp only [intPart, addPart, additive, hwdef, hzdef]
    ring
  have havg0 : avg (intPart f) = 0 := by
    have hsum : (∑ x : α × β, intPart f x) = 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun a _ => hrow a)]
      simp
    simp only [avg, hsum, zero_div]
  -- c72e84ea, spliced
  have hcross : avg (fun x : α × β => intPart f x * additive w z x) = 0 := by
    have hsum : (∑ x : α × β, intPart f x * additive w z x) = 0 := by
      rw [Fintype.sum_prod_type]
      have step : ∀ a : α, (∑ b : β, intPart f (a, b) * additive w z (a, b))
          = (∑ b : β, intPart f (a, b)) * w a + ∑ b : β, intPart f (a, b) * z b := by
        intro a
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun b _ => by simp only [additive]; ring)
      simp only [step, hrow, zero_mul, zero_add]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
    simp only [avg, hsum, zero_div]
  have hsq : 0 ≤ avg (fun x : α × β => additive w z x * additive w z x) := by
    simp only [avg]
    apply div_nonneg (Finset.sum_nonneg (fun x _ => mul_self_nonneg _))
    positivity
  have hexp : ∀ x : α × β, (f x - additive u v x) * (f x - additive u v x)
      = intPart f x * intPart f x + 2 * (intPart f x * additive w z x)
        + additive w z x * additive w z x := by
    intro x; rw [hsplit x]; ring
  have hmsse : msse f (additive u v)
      = avg (fun x : α × β => intPart f x * intPart f x)
        + 2 * avg (fun x : α × β => intPart f x * additive w z x)
        + avg (fun x : α × β => additive w z x * additive w z x) := by
    simp only [msse, avg]
    rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    field_simp
  have hvarr : varr (intPart f) = avg (fun x : α × β => intPart f x * intPart f x) := by
    simp only [varr, cov, havg0]
    ring
  rw [hvarr, hmsse, hcross]
  linarith [hsq]
