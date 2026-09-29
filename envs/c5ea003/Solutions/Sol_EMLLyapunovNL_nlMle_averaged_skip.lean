-- Prove2me | solution 1 for EMLLyapunovNL.nlMle_averaged_skip
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:31:56.895981+00:00
-- url     : https://prove2.me/submissions/b19fd1a7-d20e-410b-80f1-bbfe0be6cbe5

-- Sol generated from Novelty/EMLLyapunovTropical.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovTropical
import Theorems.Thm_EMLLyapunovNL_dist_le_of_monotone_graded

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

/-- A lower bound valid for every admissible constant bounds the optimal one. -/
lemma le_optLip {g : α → α} {L : ℝ} (hne : (lipSet g).Nonempty)
    (h : ∀ K ∈ lipSet g, L ≤ K) : L ≤ optLip g :=
  le_csInf hne h






/-! ## 2.  Saturated-activation recurrent cells -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]









/-! ## 3.  A universal edge-of-chaos theorem for monotone, translation-homogeneous cells

Many recurrent EML primitives share two structural features: they are **monotone** (larger
inputs give larger outputs) and **translation homogeneous** (a uniform shift of the state
shifts the output by the same amount).  Max-plus (tropical) layers, min-plus layers,
maxout units, and row-stochastic attention/averaging layers are all of this type.  We prove
once and for all that any such cell has maximum Lyapunov exponent **exactly zero**.
-/


variable {m : Type*} [Fintype m] [Nonempty m]


/-- Distance to a uniform shift. -/
lemma dist_add_const (x : m → ℝ) (c : ℝ) : dist (x + fun _ => c) x = |c| := by
  rw [dist_eq_norm]
  simp








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




omit [Fintype m] [Nonempty m] in
/-- Grades multiply along iterates: the `T`-fold iterate has grade `s ^ T`. -/
theorem gradedHomogeneous_iterate {s : ℝ} {f : (m → ℝ) → (m → ℝ)}
    (hhom : GradedHomogeneous s f) (T : ℕ) : GradedHomogeneous (s ^ T) f^[T] := by
  induction T with
  | zero => intro x c; simp
  | succ T ih =>
      intro x c
      rw [Function.iterate_succ_apply, hhom x c, ih (f x) (s * c),
        Function.iterate_succ_apply]
      congr 1
      funext i
      rw [pow_succ]
      ring

omit [Fintype m] [Nonempty m] in
/-- Monotonicity passes to iterates. -/
theorem monotone_iterate_of_monotone {f : (m → ℝ) → (m → ℝ)} (hmono : Monotone f) (T : ℕ) :
    Monotone f^[T] := by
  induction T with
  | zero => simpa using monotone_id
  | succ T ih =>
      rw [Function.iterate_succ]
      exact ih.comp hmono

/-- **Exact optimal Lipschitz constant of a graded cell.**  Uniform shifts saturate the
bound, so the constant of the `T`-fold iterate is exactly `s ^ T`. -/
theorem optLip_iterate_eq_of_monotone_graded {s : ℝ} (hs : 0 ≤ s) {f : (m → ℝ) → (m → ℝ)}
    (hmono : Monotone f) (hhom : GradedHomogeneous s f) (T : ℕ) : optLip f^[T] = s ^ T := by
  have hlip : ∀ x y : m → ℝ, dist (f^[T] x) (f^[T] y) ≤ s ^ T * dist x y :=
    dist_le_of_monotone_graded (pow_nonneg hs T) (monotone_iterate_of_monotone hmono T)
      (gradedHomogeneous_iterate hhom T)
  refine le_antisymm (optLip_le (pow_nonneg hs T) hlip) ?_
  refine le_optLip ⟨s ^ T, pow_nonneg hs T, hlip⟩ ?_
  rintro K ⟨hK0, hK⟩
  have h1 := hK ((0 : m → ℝ) + fun _ => (1:ℝ)) 0
  rw [gradedHomogeneous_iterate hhom T (0 : m → ℝ) 1, dist_add_const, dist_add_const] at h1
  simpa [abs_of_nonneg (pow_nonneg hs T)] using h1

/-- **Graded exponent theorem.**  The maximum Lyapunov exponent of a monotone cell of
grade `s > 0` is exactly `log s`.  Grade `1` recovers the edge-of-chaos theorem of §3. -/
theorem nlMle_eq_log_of_monotone_graded {s : ℝ} (hs : 0 < s) {f : (m → ℝ) → (m → ℝ)}
    (hmono : Monotone f) (hhom : GradedHomogeneous s f) : nlMle f = Real.log s := by
  have hftle : ∀ T : ℕ, 0 < T → nlFtle f T = Real.log s := by
    intro T hT
    have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    rw [nlFtle, optLip_iterate_eq_of_monotone_graded hs.le hmono hhom, Real.log_pow]
    field_simp
  rw [nlMle]
  refine Filter.Tendsto.limsup_eq ?_
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := Real.log s) (f := Filter.atTop))
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (hftle T hT).symm







open EMLLyapunovNL in
theorem solution{f : (m → ℝ) → (m → ℝ)} (hmono : Monotone f)
    (hhom : TranslationHomogeneous f) : nlMle (fun x => (2:ℝ)⁻¹ • (x + f x)) = 0 := by
  have hg : GradedHomogeneous 1 (fun x => (2:ℝ)⁻¹ • (x + f x)) := by
    intro x c
    show (2:ℝ)⁻¹ • ((x + fun _ => c) + f (x + fun _ => c))
        = (2:ℝ)⁻¹ • (x + f x) + fun _ => 1 * c
    rw [hhom x c]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm : Monotone (fun x => (2:ℝ)⁻¹ • (x + f x)) := by
    intro x y h
    refine fun j => ?_
    have h1 := h j
    have h2 := hmono h j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    linarith
  simpa using nlMle_eq_log_of_monotone_graded one_pos hm hg
