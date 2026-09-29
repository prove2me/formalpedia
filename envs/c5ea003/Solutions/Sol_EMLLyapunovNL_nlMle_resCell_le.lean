-- Prove2me | solution 1 for EMLLyapunovNL.nlMle_resCell_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:31:58.433324+00:00
-- url     : https://prove2.me/submissions/41faf47f-7d7b-4564-b173-0c529fa013d9

-- Sol generated from Novelty/EMLLyapunovTropical.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovTropical

/-!
# Lyapunov Exponents for Recurrent EML Architectures II: nonlinear and tropical cells

The linear theory (companion file `EMLLyapunovStability.lean`) measures gradient growth by
the norm of a Jacobian product.  For a *nonlinear* recurrent cell the right global object
is the **optimal Lipschitz constant** of the `T`-fold iterate,

`optLip f^[T] = inf {K ≥ 0 | ∀ x y, dist (f^[T] x) (f^[T] y) ≤ K * dist x y}`,

whose logarithmic growth rate is the (global, sup-norm) maximum Lyapunov exponent.  This
file proves two things.

1. **Saturated-activation cells.**  For `f = σ ∘ (W · + b)` with a `1`-Lipschitz
   activation `σ` (`tanh`, `ReLU`, hard-sigmoid, …) all iterates are `‖W‖ ^ T`-Lipschitz,
   the exponent is at most `log ‖W‖`, and the derivative of the unrolled network obeys
   `‖D(f^[T])‖ ≤ ‖W‖ ^ T` — a genuine non-exploding-gradient guarantee at the level of
   backpropagation, not merely of trajectories.

2. **A universal edge-of-chaos theorem.**  Any cell that is *monotone* and *translation
   homogeneous* is automatically non-expansive in the sup norm (a Crandall–Tartar type
   argument), and its Lipschitz constant is *exactly* `1` because uniform shifts are
   transported exactly.  Hence its maximum Lyapunov exponent is **exactly `0`**, with no
   hypothesis on the weights at all.  Two families of EML primitives are covered:

   * max-plus (tropical) cells `x ↦ (⨆ j, A i j + x j)_i`, the tropical analogue of a
     linear RNN — a bridge between tropical algebra and dynamical stability;
   * row-stochastic mixing cells `x ↦ (∑ j, P i j x j)_i`, the linear part of attention,
     averaging and consensus layers.

## Main results

* `optLip_le`, `le_optLip`, `optLip_eq_one` — calculus of the optimal Lipschitz constant.
* `lipschitzWith_emlCell`, `lipschitzWith_emlCell_iterate` — contraction budget of a
  saturated-activation recurrent cell.
* `norm_fderiv_emlCell_iterate_le` — the backpropagated derivative bound.
* `nlFtle_emlCell_le` — Lyapunov exponent bound `≤ log ‖W‖`.
* `exists_fixedPoint_emlCell` — a strict budget yields a unique stable memory state.
* `lipschitzWith_one_of_monotone_homogeneous`, `optLip_iterate_eq_one`,
  `nlMle_eq_zero_of_monotone_homogeneous` — the universal edge-of-chaos theorem.
* `lipschitzWith_one_tropCell`, `optLip_tropCell_iterate_eq_one`, `nlFtle_tropCell`,
  `nlMle_tropCell` — the tropical cell has maximum Lyapunov exponent exactly `0`.
* `nlMle_stochCell` — row-stochastic attention/averaging cells have exponent exactly `0`.
* `nlMle_dilationCell` — sharpness: translation homogeneity cannot be dropped.
* `nlMle_resCell_le`, `dist_resCell_iterate_le_exp`, `norm_fderiv_resCell_iterate_le_exp`,
  `nlMle_resCell_dilation` — residual (skip-connection) cells: the exact budget
  `log (1 + ‖W‖)`, and a *depth-uniform* gradient bound `exp c` under the critical
  depth scaling `‖W‖ ≤ c / T`.
* `GradedHomogeneous`, `nlMle_eq_log_of_monotone_graded` — the graded exponent theorem: a
  monotone cell answering a uniform shift `c` by `s · c` has exponent *exactly* `log s`.
* `nlMle_skip_eq_log_two`, `nlMle_averaged_skip` — a skip connection on any monotone
  homogeneous branch has exponent exactly `log 2`, and halving the sum restores `0`.
-/

open Filter Topology

open EMLLyapunovNL

/-! ## 1.  The optimal Lipschitz constant and the nonlinear Lyapunov exponent -/



variable {α : Type*} [PseudoMetricSpace α]

lemma lipSet_bddBelow (g : α → α) : BddBelow (lipSet g) := ⟨0, fun _ hx => hx.1⟩

/-- Any admissible constant dominates the optimal one. -/
lemma optLip_le {g : α → α} {K : ℝ} (hK : 0 ≤ K) (h : ∀ x y, dist (g x) (g y) ≤ K * dist x y) :
    optLip g ≤ K :=
  csInf_le (lipSet_bddBelow g) ⟨hK, h⟩






/-- A `limsup` comparison that survives the `ℝ`-valued junk conventions: an eventual upper
bound `M ≥ 0` bounds the `limsup`, even when the sequence is unbounded below (in which case
Mathlib's real `sInf` returns `0 ≤ M`). -/
lemma limsup_le_of_nonneg_of_eventually_le {u : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ᶠ T in Filter.atTop, u T ≤ M) : limsup u Filter.atTop ≤ M := by
  rw [Filter.limsup_eq]
  by_cases hb : BddBelow {a : ℝ | ∀ᶠ T in Filter.atTop, u T ≤ a}
  · exact csInf_le hb h
  · rw [Real.sInf_of_not_bddBelow hb]
    exact hM

/-! ## 2.  Saturated-activation recurrent cells -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- With a `1`-Lipschitz activation, a recurrent EML cell is `‖W‖`-Lipschitz. -/
theorem lipschitzWith_emlCell (W : E →L[ℝ] E) (b : E) {σ : E → E} (hσ : LipschitzWith 1 σ) :
    LipschitzWith ‖W‖₊ (emlCell W b σ) := by
  have h1 : LipschitzWith ‖W‖₊ (fun x : E => W x + b) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact W.le_opNorm _
  simpa [emlCell] using (hσ.comp h1)







/-! ## 3.  A universal edge-of-chaos theorem for monotone, translation-homogeneous cells

Many recurrent EML primitives share two structural features: they are **monotone** (larger
inputs give larger outputs) and **translation homogeneous** (a uniform shift of the state
shifts the output by the same amount).  Max-plus (tropical) layers, min-plus layers,
maxout units, and row-stochastic attention/averaging layers are all of this type.  We prove
once and for all that any such cell has maximum Lyapunov exponent **exactly zero**.
-/


variable {m : Type*} [Fintype m] [Nonempty m]










/-! ## 4.  Tropical (max-plus) recurrent cells -/


variable {m : Type*} [Fintype m] [Nonempty m]









/-! ## 5.  Row-stochastic (attention / averaging) recurrent cells -/


variable {m : Type*} [Fintype m] [Nonempty m]






/-! ## 6.  Sharpness: dropping translation homogeneity breaks the theorem

A pure dilation `x ↦ r • x` is monotone (on the coordinatewise order) but *not*
translation homogeneous unless `r = 1`, and its exponent is exactly `log |r|`.  Taking
`r = 2` exhibits a monotone cell with a strictly positive exponent, so translation
homogeneity is not removable from `nlMle_eq_zero_of_monotone_homogeneous`.
-/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]






/-! ## 7.  Residual (skip-connection) cells and depth-scaled non-explosion

Modern deep EML stacks are *residual*: `x ↦ x + σ (W x + b)`.  The skip connection costs
one unit of Lipschitz budget, so the naive bound `(1 + ‖W‖) ^ T` still explodes with depth
for any fixed nonzero `W`.  The point of this section is that the explosion is *exactly*
compensated by the standard depth scaling `‖W‖ ≤ c / T`: then

`(1 + c/T) ^ T ≤ exp c`

uniformly in `T`, so a depth-`T` residual EML network with depth-scaled weights has
backpropagated gradients bounded by `exp c` at *every* depth and *every* point.  The final
theorem shows this budget is attained, so `log (1 + ‖W‖)` is the exact exponent, not merely
an upper bound.
-/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- The skip connection costs exactly one unit of Lipschitz budget. -/
theorem lipschitzWith_resCell (W : E →L[ℝ] E) (b : E) {σ : E → E} (hσ : LipschitzWith 1 σ) :
    LipschitzWith (1 + ‖W‖₊) (resCell W b σ) := by
  have hbranch : LipschitzWith ‖W‖₊ (emlCell W b σ) := lipschitzWith_emlCell W b hσ
  have := (LipschitzWith.id (α := E)).add hbranch
  simpa [resCell, emlCell, Function.id_def] using this

/-- Unrolling a residual cell to depth `T` costs `(1 + ‖W‖) ^ T`. -/
theorem lipschitzWith_resCell_iterate (W : E →L[ℝ] E) (b : E) {σ : E → E}
    (hσ : LipschitzWith 1 σ) (T : ℕ) :
    LipschitzWith ((1 + ‖W‖₊) ^ T) (resCell W b σ)^[T] :=
  (lipschitzWith_resCell W b hσ).iterate T

/-- The optimal Lipschitz constant of the unrolled residual network. -/
theorem optLip_resCell_iterate_le (W : E →L[ℝ] E) (b : E) {σ : E → E} (hσ : LipschitzWith 1 σ)
    (T : ℕ) : optLip (resCell W b σ)^[T] ≤ (1 + ‖W‖) ^ T := by
  refine optLip_le (by positivity) (fun x y => ?_)
  have h := (lipschitzWith_resCell_iterate W b hσ T).dist_le_mul x y
  simpa using h






/-! ## 8.  Graded homogeneity: skip connections are incompatible with the edge of chaos

Section 3 shows that a monotone cell whose response to a uniform shift `c` is again the
shift `c` sits exactly at the edge of chaos.  Section 7 shows that a residual cell can
explode.  Both are instances of one graded statement: if a monotone cell answers a uniform
shift `c` by the shift `s · c`, its maximum Lyapunov exponent is **exactly** `log s`.  The
grade `s` is a *multiplicative character of the shift action*, and the exponent reads it
off directly — no spectral information about the cell is used.

Two consequences are worth naming.  Adding an identity skip connection to any monotone,
translation-homogeneous branch doubles the grade, giving exponent exactly `log 2`
regardless of the weights: **skip connections cannot be at the edge of chaos**.  Dividing
the sum by two restores grade `1` and exponent exactly `0`, so the averaged skip
`x ↦ (x + f x)/2` is the unique convex repair.
-/


variable {m : Type*} [Fintype m] [Nonempty m]














open EMLLyapunovNL in
theorem solution(W : E →L[ℝ] E) (b : E) {σ : E → E} (hσ : LipschitzWith 1 σ) :
    nlMle (resCell W b σ) ≤ Real.log (1 + ‖W‖) := by
  have hM : 0 ≤ Real.log (1 + ‖W‖) := Real.log_nonneg (by linarith [norm_nonneg W])
  refine limsup_le_of_nonneg_of_eventually_le hM ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hmem : (1 + ‖W‖) ^ T ∈ lipSet (resCell W b σ)^[T] :=
    ⟨by positivity, fun x y => by
      simpa using (lipschitzWith_resCell_iterate W b hσ T).dist_le_mul x y⟩
  have hnn : 0 ≤ optLip (resCell W b σ)^[T] := le_csInf ⟨_, hmem⟩ (fun K hK => hK.1)
  have hle := optLip_resCell_iterate_le W b hσ T
  rcases eq_or_lt_of_le hnn with h0 | h0
  · rw [nlFtle, ← h0, Real.log_zero, mul_zero]
    exact hM
  · have hlog : Real.log (optLip (resCell W b σ)^[T]) ≤ (T : ℝ) * Real.log (1 + ‖W‖) := by
      have := Real.log_le_log h0 hle
      rwa [Real.log_pow] at this
    rw [nlFtle, inv_mul_le_iff₀ hT']
    linarith
