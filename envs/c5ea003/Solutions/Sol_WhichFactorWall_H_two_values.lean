-- Prove2me | solution 1 for WhichFactorWall.H_two_values
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:26.18889+00:00
-- url     : https://prove2.me/submissions/244fd128-a1a2-41fc-9069-ebe9532eb98b

-- Sol generated from Algebra/WhichFactorWallInvariant.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
/-
# The which-factor wall as a cross-population invariant: how much does it really pin down?

This file continues `Speculative.AutoResearch.TraceBatteryWall`
(`TraceBattery.binary_wall_inversion`), which shows that a *binary* capacity
("wall") value determines the class imbalance of a two-valued statistic
**uniquely** on the balanced side `[0, 1/2]`.  Uniqueness, however, is a
qualitative statement.  The research question of this cycle is quantitative:

> if two independent populations report walls that agree to within `ε`,
> how close are their class imbalances?

The mission proposal was:

  `|binEntropy p - binEntropy q| ≥ c(δ) |p - q|` on `[δ, 1/2]`,
  with `c(δ) = log ((1-δ)/δ)`.

**This is false**, and `binEntropy_conjectured_lower_bound_false` refutes it with
an exact counterexample (`δ = q = 1/4`, `p = 1/2`), where the failure reduces to
`log 16 ≤ log 27`.  The reason is structural: `c(δ)` is the *supremum* of
`|binEntropy'|` on `[δ, 1/2]`, not its infimum, so it controls the Lipschitz
(upper) bound, while the true inverse bound must be governed by the derivative
at the endpoint *closest to* `1/2`.

What survives, and is proved here with zero sorries:

* `binEntropy_sub_ge` — the sharp mean-value lower bound
  `(q - p) * (log (1-q) - log q) ≤ binEntropy q - binEntropy p` for
  `0 ≤ p ≤ q ≤ 1/2` (including the boundary case `p = 0`).
* `binEntropy_lipschitz` — the true version of the proposed inequality, with the
  inequality reversed: `|binEntropy p - binEntropy q| ≤ c(δ) |p - q|` on
  `[δ, 1-δ]`.
* `imbalance_dist_le` / `imbalance_dist_le_div` — the corrected **cross-population
  stability theorem**: imbalances in `[0, 1/2 - η]` whose walls agree within `ε`
  agree within `ε / log ((1/2+η)/(1/2-η))`.
* `binary_wall_stability` — the same statement at the level of two binary
  statistics on two different finite populations, via the empirical entropy `H`.
* `log_two_sub_binEntropy_le_sq` — `log 2 - binEntropy (1/2 - t) ≤ 4 t²`, and
  `no_uniform_inversion_constant`: **no** constant inverts the wall near `1/2`.
  So the guard `η > 0` is not an artefact: the wall genuinely loses all
  resolution at balance, at a quadratic rate.
* `wall_imbalance_bracket` — the reported wall `0.4677` bits is a falsifiable
  claim about the split: the unique minority fraction in `[0, 1/2]` realising it
  lies strictly between `1/12` and `1/9` (i.e. between 8.34% and 11.11%),
  consistent with the reported 9.96% and inconsistent with, say, a 5% or a 15%
  split.

Because the catalog module `Combinatorics.TraceBatteryEntropy` carrying the
empirical-entropy definitions is not present in this snapshot, the small
population layer (`img`, `cnt`, `H`, `H_two_values`) is restated here in the
open `WhichFactorWall`,
self-contained and compiles on its own.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  Mean-value machinery for `Real.binEntropy`

`binEntropy` is differentiable away from `{0,1}` with derivative
`log (1-x) - log x` (Mathlib's `Real.deriv_binEntropy`).  We turn one-sided
bounds on that derivative into slope bounds by monotonicity of an auxiliary
function; this is the mean value theorem in the form we need. -/







/-! ## 2.  Refutation of the proposed inverse bound -/


/-! ## 3.  Corrected cross-population stability -/



/-! ## 4.  Why the guard `η > 0` cannot be dropped: quadratic degeneracy at balance -/



/-! ## 5.  Population layer: empirical entropy of a two-valued statistic

These are the definitions of the catalog's trace-battery entropy module,
restated so that this file is self-contained. -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}




variable [DecidableEq α]

omit [Nonempty Ω] in
lemma sum_cnt (f : Ω → α) : ∑ a ∈ img f, cnt f a = Fintype.card Ω := by
  classical
  simp only [cnt, img]
  rw [← Finset.card_univ (α := Ω)]
  exact (Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
    (t := Finset.image f Finset.univ)
    (fun x _ => Finset.mem_image_of_mem f (Finset.mem_univ x))).symm

omit [Nonempty Ω] in
lemma cnt_pos_of_mem_img {f : Ω → α} {a : α} (h : a ∈ img f) : 0 < cnt f a := by
  rw [img] at h
  obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h
  rw [cnt, Finset.card_pos]
  exact ⟨w, by simp [hw]⟩




/-! ## 6.  The reported wall `0.4677` bits as a falsifiable claim about the split -/













theorem solution (f : Ω → α) {a b : α} (hab : a ≠ b) (himg : img f = {a, b}) :
    H f = Real.binEntropy ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) := by
  classical
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hamem : a ∈ img f := by rw [himg]; exact Finset.mem_insert_self a {b}
  have hbmem : b ∈ img f := by
    rw [himg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hapos : (0 : ℝ) < cnt f a := by exact_mod_cast cnt_pos_of_mem_img hamem
  have hbpos : (0 : ℝ) < cnt f b := by exact_mod_cast cnt_pos_of_mem_img hbmem
  have hsum : (cnt f a : ℝ) + cnt f b = (Fintype.card Ω : ℝ) := by
    have h := sum_cnt f
    rw [himg, Finset.sum_pair hab] at h
    exact_mod_cast h
  have hHf : H f = ((cnt f a : ℝ) / (Fintype.card Ω : ℝ))
        * Real.log ((Fintype.card Ω : ℝ) / cnt f a)
      + ((cnt f b : ℝ) / (Fintype.card Ω : ℝ))
        * Real.log ((Fintype.card Ω : ℝ) / cnt f b) := by
    rw [H, himg, Finset.sum_pair hab]
  set p : ℝ := (cnt f a : ℝ) / (Fintype.card Ω : ℝ) with hp
  have hp0 : 0 < p := by rw [hp]; positivity
  have h1p : 1 - p = (cnt f b : ℝ) / (Fintype.card Ω : ℝ) := by
    rw [hp]; field_simp; linarith [hsum]
  have hinvp : p⁻¹ = (Fintype.card Ω : ℝ) / cnt f a := by rw [hp, inv_div]
  have hinvq : (1 - p)⁻¹ = (Fintype.card Ω : ℝ) / cnt f b := by rw [h1p, inv_div]
  rw [hHf, Real.binEntropy, hinvp, ← h1p, hinvq, h1p]
