-- Prove2me | solution 1 for LinearOptimization.interior_point_path_following_iterations
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-08-06T21:32:40.892254+00:00
-- url     : https://prove2.me/submissions/a26bb57b-7248-408e-9430-e73cbcbfb71d

import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_LinearOptimization_PathFollowing

/-!
# Theorem 9.7 (Bertsimas & Tsitsiklis, p. 428)

The primal path following algorithm reaches duality gap `ε` in
`K = ⌈(√β+√n)/(√β−β) · log((s⁰)'x⁰(1+β)/(ε(1−β)))⌉` iterations.

The heart is the invariant of Theorem 9.6: `β`-closeness is preserved.
Writing `Dⱼ = dⱼ/xⱼ`, the Newton equations give
`s'ⱼ = (μ'/xⱼ)(1 − Dⱼ)` and `x'ⱼ = xⱼ(1 + Dⱼ)`, so
`x'ⱼs'ⱼ = μ'(1 − Dⱼ²)` and the new proximity is `‖D²‖ ≤ ‖D‖²`.
A Pythagoras argument (using `Ad = 0`) bounds `μ'‖D‖ ≤ ‖μ'e − XSe‖`, and the
choice of `α` makes the resulting bound exactly `√β`.
-/

open Matrix

namespace PF

open LinearOptimization

variable {m n : ℕ}

/-! ### A Euclidean norm on `Fin n → ℝ` -/

noncomputable def nrm (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, (v j) ^ 2)

lemma sum_sq_nonneg (v : Fin n → ℝ) : 0 ≤ ∑ j, (v j) ^ 2 :=
  Finset.sum_nonneg (fun j _ => sq_nonneg _)

lemma nrm_nonneg (v : Fin n → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : Fin n → ℝ) : (nrm v) ^ 2 = ∑ j, (v j) ^ 2 :=
  Real.sq_sqrt (sum_sq_nonneg v)

lemma sum_le_sqrt_card_mul_nrm (v : Fin n → ℝ) :
    ∑ j, v j ≤ Real.sqrt (n : ℝ) * nrm v := by
  have h1 : (∑ j, v j) ^ 2 ≤ (n : ℝ) * ∑ j, (v j) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := v)
    simpa using this
  have h2 : ∑ j, v j ≤ Real.sqrt ((∑ j, v j) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
  refine h2.trans ?_
  calc Real.sqrt ((∑ j, v j) ^ 2) ≤ Real.sqrt ((n : ℝ) * ∑ j, (v j) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt (n : ℝ) * nrm v := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n)]
        rfl

/-- `‖a‖₂ ≤ ‖a‖₁` for a nonnegative vector. -/
lemma nrm_sq_vec_le (a : Fin n → ℝ) :
    nrm (fun j => (a j) ^ 2) ≤ ∑ j, (a j) ^ 2 := by
  have h1 : ∑ j, ((a j) ^ 2) ^ 2 ≤ (∑ j, (a j) ^ 2) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => sq_nonneg _)
  calc nrm (fun j => (a j) ^ 2) = Real.sqrt (∑ j, ((a j) ^ 2) ^ 2) := rfl
    _ ≤ Real.sqrt ((∑ j, (a j) ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∑ j, (a j) ^ 2 := by
        rw [Real.sqrt_sq (sum_sq_nonneg a)]

lemma transpose_dot (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) (y : Fin n → ℝ) :
    (Aᵀ.mulVec q) ⬝ᵥ y = q ⬝ᵥ (A.mulVec y) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-! ### The shrinking factor -/

/-- `α = (√n + β)/(√β + √n)`, and `β + (1−α)√n = α√β`. -/
lemma alpha_form {beta alpha : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (halpha : alpha = 1 - (Real.sqrt beta - beta) / (Real.sqrt beta + Real.sqrt (n : ℝ))) :
    0 < alpha ∧ alpha < 1 ∧ beta + (1 - alpha) * Real.sqrt (n : ℝ) = alpha * Real.sqrt beta := by
  have hsb : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta0
  have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt beta + Real.sqrt (n : ℝ) := by linarith
  have hsbsq : Real.sqrt beta * Real.sqrt beta = beta := Real.mul_self_sqrt hbeta0.le
  have hsblt : beta < Real.sqrt beta := by
    nlinarith [hsbsq, hsb, hbeta1]
  have halpha' : alpha = (Real.sqrt (n : ℝ) + beta) / (Real.sqrt beta + Real.sqrt (n : ℝ)) := by
    rw [halpha]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [halpha']
    exact div_pos (by linarith) hden
  · rw [halpha]
    have : 0 < (Real.sqrt beta - beta) / (Real.sqrt beta + Real.sqrt (n : ℝ)) :=
      div_pos (by linarith) hden
    linarith
  · rw [halpha']
    field_simp
    nlinarith [hsbsq]

/-! ### One Newton step preserves `β`-closeness -/

lemma step_inv (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    {beta alpha : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (halpha : alpha = 1 - (Real.sqrt beta - beta) / (Real.sqrt beta + Real.sqrt (n : ℝ)))
    {mu mu' : ℝ} (hmu : 0 < mu) (hmu' : mu' = alpha * mu)
    {xk : Fin n → ℝ} {pk : Fin m → ℝ} {sk : Fin n → ℝ}
    (hxk : ∀ j, 0 < xk j) (hdualk : Aᵀ.mulVec pk + sk = c)
    (hprox : centralPathProximity mu xk sk ≤ beta)
    {d : Fin n → ℝ} {p' : Fin m → ℝ}
    (hnewton : IsNewtonBarrierStep A c mu' xk d p')
    {x' s' : Fin n → ℝ} (hx' : x' = xk + d) (hs' : s' = c - Aᵀ.mulVec p')
    (hx'pos : ∀ j, 0 < x' j) :
    centralPathProximity mu' x' s' ≤ beta ∧ (∀ j, 0 < s' j) := by
  obtain ⟨hapos, halt1, hkey⟩ := alpha_form (n := n) hbeta0 hbeta1 halpha
  have hmu'pos : 0 < mu' := by rw [hmu']; exact mul_pos hapos hmu
  set D : Fin n → ℝ := fun j => d j / xk j with hD
  -- the Newton equations, entrywise
  have hnew : ∀ j, s' j = mu' / xk j - mu' * d j / (xk j) ^ 2 := by
    intro j
    have h := congrFun hnewton.1 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, mul_one] at h
    rw [hs']
    simp only [Pi.sub_apply]
    have e1 : mu' / xk j = mu' * (xk j)⁻¹ := by ring
    have e2 : mu' * d j / (xk j) ^ 2 = mu' * ((xk j ^ 2)⁻¹ * d j) := by ring
    rw [e1, e2]
    linarith
  have hxne : ∀ j, xk j ≠ 0 := fun j => ne_of_gt (hxk j)
  have hs'eq : ∀ j, s' j = mu' / xk j * (1 - D j) := by
    intro j
    have hx := hxne j
    rw [hnew j, hD]
    field_simp
  have hx'eq : ∀ j, x' j = xk j * (1 + D j) := by
    intro j
    have hx := hxne j
    rw [hx', hD]
    simp only [Pi.add_apply]
    field_simp
  have hprod : ∀ j, x' j * s' j = mu' * (1 - (D j) ^ 2) := by
    intro j
    have hx := hxne j
    rw [hx'eq j, hs'eq j]
    field_simp
    ring
  -- Pythagoras: `μ'‖D‖ ≤ ‖μ'e − X S e‖`
  have hpyth : mu' ^ 2 * ∑ j, (D j) ^ 2 ≤ ∑ j, (mu' - xk j * sk j) ^ 2 := by
    set q : Fin m → ℝ := p' - pk with hq
    set w : Fin n → ℝ := fun j => xk j * (Aᵀ.mulVec q) j with hw
    have hsplit : ∀ j, mu' * D j = (mu' - xk j * sk j) + w j := by
      intro j
      have hx := hxne j
      have h1 : xk j * s' j = mu' * (1 - D j) := by
        rw [hs'eq j]; field_simp
      have h2 : s' j = sk j - (Aᵀ.mulVec q) j := by
        have hc : c j = (Aᵀ.mulVec pk) j + sk j := by
          have := congrFun hdualk j
          simp only [Pi.add_apply] at this
          linarith
        rw [hs', hq]
        simp only [Pi.sub_apply, hc]
        have : (Aᵀ.mulVec (p' - pk)) j = (Aᵀ.mulVec p') j - (Aᵀ.mulVec pk) j := by
          simp [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        rw [this]
        ring
      rw [hw]
      have := h1
      rw [h2] at this
      simp only
      nlinarith [this]
    have horth : ∑ j, D j * w j = 0 := by
      have : ∑ j, D j * w j = ∑ j, (Aᵀ.mulVec q) j * d j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hw, hD]
        have hx := hxne j
        field_simp
      rw [this]
      have h3 : (Aᵀ.mulVec q) ⬝ᵥ d = q ⬝ᵥ (A.mulVec d) := transpose_dot A q d
      rw [hnewton.2] at h3
      simpa [dotProduct] using h3
    have hexp : ∑ j, (mu' - xk j * sk j) ^ 2
        = ∑ j, (mu' * D j) ^ 2 + ∑ j, (w j) ^ 2 := by
      have hv : ∀ j, mu' - xk j * sk j = mu' * D j - w j := fun j => by
        have := hsplit j; linarith
      rw [Finset.sum_congr rfl (fun j _ => by rw [hv j] : ∀ j ∈ Finset.univ,
        (mu' - xk j * sk j) ^ 2 = (mu' * D j - w j) ^ 2)]
      have : ∀ j, (mu' * D j - w j) ^ 2
          = (mu' * D j) ^ 2 - 2 * mu' * (D j * w j) + (w j) ^ 2 := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, horth]
      ring
    have hwnn : 0 ≤ ∑ j, (w j) ^ 2 := sum_sq_nonneg w
    have hmuD : ∑ j, (mu' * D j) ^ 2 = mu' ^ 2 * ∑ j, (D j) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hexp, hmuD]
    linarith
  -- turn the bound into `∑ Dⱼ² ≤ β`
  set wk : Fin n → ℝ := fun j => xk j * sk j / mu - 1 with hwk
  have hproxsq : ∑ j, (wk j) ^ 2 ≤ beta ^ 2 := by
    have h1 : Real.sqrt (∑ j, (wk j) ^ 2) ≤ beta := hprox
    have h2 := Real.sq_sqrt (sum_sq_nonneg wk)
    nlinarith [Real.sqrt_nonneg (∑ j, (wk j) ^ 2)]
  have hvform : ∀ j, mu' - xk j * sk j = -(mu * (wk j + (1 - alpha))) := by
    intro j
    rw [hwk, hmu']
    field_simp
    ring
  have hsumv : ∑ j, (mu' - xk j * sk j) ^ 2
      = mu ^ 2 * ∑ j, (wk j + (1 - alpha)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hvform j]
    ring
  have hbnd : ∑ j, (wk j + (1 - alpha)) ^ 2 ≤ (beta + (1 - alpha) * Real.sqrt (n : ℝ)) ^ 2 := by
    have hexp : ∑ j, (wk j + (1 - alpha)) ^ 2
        = (∑ j, (wk j) ^ 2) + 2 * (1 - alpha) * (∑ j, wk j) + (n : ℝ) * (1 - alpha) ^ 2 := by
      have : ∀ j, (wk j + (1 - alpha)) ^ 2
          = (wk j) ^ 2 + 2 * (1 - alpha) * wk j + (1 - alpha) ^ 2 := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hsumwk : ∑ j, wk j ≤ Real.sqrt (n : ℝ) * beta := by
      refine le_trans (sum_le_sqrt_card_mul_nrm wk) ?_
      have : nrm wk ≤ beta := hprox
      exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
    have h1a : 0 ≤ 1 - alpha := by linarith
    have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hnsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    rw [hexp]
    nlinarith [hproxsq, hsumwk, h1a, hsn, hnsq]
  have hDsum : ∑ j, (D j) ^ 2 ≤ beta := by
    have h1 : mu' ^ 2 * ∑ j, (D j) ^ 2 ≤ mu ^ 2 * (alpha * Real.sqrt beta) ^ 2 := by
      rw [← hkey]
      calc mu' ^ 2 * ∑ j, (D j) ^ 2 ≤ ∑ j, (mu' - xk j * sk j) ^ 2 := hpyth
        _ = mu ^ 2 * ∑ j, (wk j + (1 - alpha)) ^ 2 := hsumv
        _ ≤ mu ^ 2 * (beta + (1 - alpha) * Real.sqrt (n : ℝ)) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hbnd (sq_nonneg mu)
    have hmu'sq : mu' ^ 2 = alpha ^ 2 * mu ^ 2 := by rw [hmu']; ring
    have hsbsq : Real.sqrt beta ^ 2 = beta := Real.sq_sqrt hbeta0.le
    rw [hmu'sq] at h1
    have hpos : 0 < alpha ^ 2 * mu ^ 2 := mul_pos (pow_pos hapos 2) (pow_pos hmu 2)
    nlinarith [h1, hsbsq, hpos]
  -- conclude
  have hs'pos : ∀ j, 0 < s' j := by
    intro j
    have hDj : (D j) ^ 2 ≤ beta := by
      refine le_trans ?_ hDsum
      exact Finset.single_le_sum (fun i _ => sq_nonneg (D i)) (Finset.mem_univ j)
    have hprodpos : 0 < x' j * s' j := by
      rw [hprod j]
      have : 0 < 1 - (D j) ^ 2 := by linarith
      positivity
    by_contra hns
    push_neg at hns
    nlinarith [hprodpos, hx'pos j, hns]
  refine ⟨?_, hs'pos⟩
  have hproxval : centralPathProximity mu' x' s' = nrm (fun j => (D j) ^ 2) := by
    simp only [centralPathProximity, nrm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hprod j]
    have : mu' * (1 - (D j) ^ 2) / mu' - 1 = -(D j) ^ 2 := by
      field_simp
      ring
    rw [this]
    ring
  rw [hproxval]
  exact le_trans (nrm_sq_vec_le D) hDsum

/-! ### Gap bounds from proximity -/

lemma gap_bounds {mu : ℝ} (hmu : 0 < mu) (xk sk : Fin n → ℝ) {beta : ℝ}
    (hprox : centralPathProximity mu xk sk ≤ beta) :
    mu * ((n : ℝ) - Real.sqrt (n : ℝ) * beta) ≤ sk ⬝ᵥ xk ∧
      sk ⬝ᵥ xk ≤ mu * ((n : ℝ) + Real.sqrt (n : ℝ) * beta) := by
  set wk : Fin n → ℝ := fun j => xk j * sk j / mu - 1 with hwk
  have hnrm : nrm wk ≤ beta := hprox
  have hdot : sk ⬝ᵥ xk = mu * ((n : ℝ) + ∑ j, wk j) := by
    have hterm : ∀ j, sk j * xk j = mu * (1 + wk j) := by
      intro j
      rw [hwk]
      field_simp
      ring
    simp only [dotProduct]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hup : ∑ j, wk j ≤ Real.sqrt (n : ℝ) * beta := by
    refine le_trans (sum_le_sqrt_card_mul_nrm wk) ?_
    exact mul_le_mul_of_nonneg_left hnrm (Real.sqrt_nonneg _)
  have hlow : -(Real.sqrt (n : ℝ) * beta) ≤ ∑ j, wk j := by
    have h1 : ∑ j, (-wk j) ≤ Real.sqrt (n : ℝ) * nrm (fun j => -wk j) :=
      sum_le_sqrt_card_mul_nrm _
    have h2 : nrm (fun j => -wk j) = nrm wk := by
      simp only [nrm]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2] at h1
    have h3 : ∑ j, (-wk j) = -∑ j, wk j := by rw [← Finset.sum_neg_distrib]
    rw [h3] at h1
    have h4 := mul_le_mul_of_nonneg_left hnrm (Real.sqrt_nonneg (n : ℝ))
    linarith
  rw [hdot]
  exact ⟨by nlinarith [hlow, hmu], by nlinarith [hup, hmu]⟩

end PF

open LinearOptimization PF
open Matrix

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (beta eps alpha : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heps : 0 < eps)
    (halpha : alpha = 1 -
      (Real.sqrt beta - beta) / (Real.sqrt beta + Real.sqrt n))
    (x : ℕ → Fin n → ℝ) (p : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (mu : ℕ → ℝ) (hmu0 : 0 < mu 0)
    (hxfeas0 : A.mulVec (x 0) = b) (hx0 : ∀ j, 0 < x 0 j)
    (hsfeas0 : Aᵀ.mulVec (p 0) + s 0 = c) (hs0 : ∀ j, 0 < s 0 j)
    (hprox0 : centralPathProximity (mu 0) (x 0) (s 0) ≤ beta)
    (hrun : IsPathFollowingRun A c alpha x p s mu)
    (K : ℕ)
    (hK : K = ⌈(Real.sqrt beta + Real.sqrt n) / (Real.sqrt beta - beta) *
      Real.log ((s 0 ⬝ᵥ x 0) * (1 + beta) / (eps * (1 - beta)))⌉₊) :
    A.mulVec (x K) = b ∧ 0 ≤ x K ∧
      Aᵀ.mulVec (p K) + s K = c ∧ 0 ≤ s K ∧
      s K ⬝ᵥ x K ≤ eps := by
  obtain ⟨hapos, halt1, hkey⟩ := alpha_form (n := n) hbeta0 hbeta1 halpha
  -- the invariant
  have inv : ∀ k, A.mulVec (x k) = b ∧ Aᵀ.mulVec (p k) + s k = c ∧ (∀ j, 0 < s k j) ∧
      0 < mu k ∧ centralPathProximity (mu k) (x k) (s k) ≤ beta ∧ mu k = alpha ^ k * mu 0 := by
    intro k
    induction k with
    | zero => exact ⟨hxfeas0, hsfeas0, hs0, hmu0, hprox0, by simp⟩
    | succ j ih =>
        obtain ⟨hb, hdual, hspos, hmupos, hpx, hmuval⟩ := ih
        obtain ⟨hxpos, hmustep, d, hnewton, hxstep, hsstep⟩ := hrun j
        have hx'pos := (hrun (j + 1)).1
        obtain ⟨hprox', hspos'⟩ :=
          step_inv A c hbeta0 hbeta1 halpha hmupos hmustep hxpos hdual hpx hnewton
            hxstep hsstep hx'pos
        refine ⟨?_, ?_, hspos', ?_, hprox', ?_⟩
        · rw [hxstep, Matrix.mulVec_add, hnewton.2, hb, add_zero]
        · rw [hsstep]; abel
        · rw [hmustep]; exact mul_pos hapos hmupos
        · rw [hmustep, hmuval]; ring
  obtain ⟨hbK, hdualK, hsposK, hmuposK, hproxK, hmuvalK⟩ := inv K
  refine ⟨hbK, fun j => (hrun K).1 j |>.le, hdualK, fun j => (hsposK j).le, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [dotProduct]
    exact heps.le
  -- `n ≥ 1`
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (n : ℝ)), Real.sqrt_nonneg (n : ℝ),
      Real.sqrt_pos.2 (by linarith : (0 : ℝ) < (n : ℝ))]
  have hsqnn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  obtain ⟨hlow0, -⟩ := gap_bounds hmu0 (x 0) (s 0) hprox0
  obtain ⟨-, hupK⟩ := gap_bounds hmuposK (x K) (s K) hproxK
  have hstart : mu 0 * ((n : ℝ) * (1 - beta)) ≤ s 0 ⬝ᵥ x 0 := by
    refine le_trans ?_ hlow0
    have : (n : ℝ) * (1 - beta) ≤ (n : ℝ) - Real.sqrt (n : ℝ) * beta := by nlinarith
    nlinarith [hmu0]
  have hs0x0 : 0 < s 0 ⬝ᵥ x 0 := by
    have : 0 < mu 0 * ((n : ℝ) * (1 - beta)) := by
      refine mul_pos hmu0 (mul_pos ?_ (by linarith))
      linarith
    linarith
  have hend : s K ⬝ᵥ x K ≤ alpha ^ K * (mu 0 * ((n : ℝ) * (1 + beta))) := by
    refine le_trans hupK ?_
    have h1 : (n : ℝ) + Real.sqrt (n : ℝ) * beta ≤ (n : ℝ) * (1 + beta) := by nlinarith
    rw [hmuvalK]
    have h2 : 0 < alpha ^ K * mu 0 := mul_pos (pow_pos hapos K) hmu0
    nlinarith [h2]
  -- the geometric factor
  set R : ℝ := (s 0 ⬝ᵥ x 0) * (1 + beta) / (eps * (1 - beta)) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact div_pos (mul_pos hs0x0 (by linarith)) (mul_pos heps (by linarith))
  have hbound : mu 0 * ((n : ℝ) * (1 + beta)) ≤ eps * R := by
    rw [hR]
    have h1 : mu 0 * ((n : ℝ) * (1 - beta)) ≤ s 0 ⬝ᵥ x 0 := hstart
    have h2 : 0 < 1 - beta := by linarith
    rw [mul_div_assoc']
    rw [le_div_iff₀ (mul_pos heps h2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ eps * (1 + beta))]
  have hpowle : alpha ^ K ≤ 1 / R := by
    by_cases hle : R ≤ 1
    · have h1 : alpha ^ K ≤ 1 := pow_le_one₀ hapos.le halt1.le
      have h2 : (1 : ℝ) ≤ 1 / R := by
        rw [le_div_iff₀ hRpos]; linarith
      linarith
    · have hlt : 1 < R := by push_neg at hle; exact hle
      have hlogR : 0 < Real.log R := Real.log_pos hlt
      have hsb : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta0
      have hsbsq : Real.sqrt beta * Real.sqrt beta = beta := Real.mul_self_sqrt hbeta0.le
      have hsblt : beta < Real.sqrt beta := by nlinarith [hsbsq, hsb, hbeta1]
      have hden : 0 < Real.sqrt beta - beta := by linarith
      have hnum : 0 < Real.sqrt beta + Real.sqrt (n : ℝ) := by linarith
      have hKge : (Real.sqrt beta + Real.sqrt (n : ℝ)) / (Real.sqrt beta - beta) *
          Real.log R ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
      have halpha1 : alpha - 1 = -((Real.sqrt beta - beta) /
          (Real.sqrt beta + Real.sqrt (n : ℝ))) := by rw [halpha]; ring
      have hloga : Real.log alpha ≤ alpha - 1 := Real.log_le_sub_one_of_pos hapos
      have hstep : (K : ℝ) * Real.log alpha ≤ -Real.log R := by
        have h1 : (K : ℝ) * Real.log alpha ≤ (K : ℝ) * (alpha - 1) :=
          mul_le_mul_of_nonneg_left hloga (Nat.cast_nonneg K)
        have h2 : (K : ℝ) * (alpha - 1) ≤ -Real.log R := by
          have hKge' : (Real.sqrt beta + Real.sqrt (n : ℝ)) * Real.log R
              ≤ (K : ℝ) * (Real.sqrt beta - beta) := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hden] at hKge
            linarith
          rw [halpha1, mul_neg, neg_le_neg_iff, mul_div_assoc', le_div_iff₀ hnum]
          nlinarith [hKge']
        linarith
      have hlogpow : Real.log (alpha ^ K) = (K : ℝ) * Real.log alpha := by
        rw [Real.log_pow]
      have hpow : 0 < alpha ^ K := pow_pos hapos K
      have hinv : 0 < 1 / R := by positivity
      rw [← Real.log_le_log_iff hpow hinv, hlogpow, one_div, Real.log_inv]
      exact hstep
  calc s K ⬝ᵥ x K ≤ alpha ^ K * (mu 0 * ((n : ℝ) * (1 + beta))) := hend
    _ ≤ alpha ^ K * (eps * R) := by
        exact mul_le_mul_of_nonneg_left hbound (pow_pos hapos K).le
    _ ≤ (1 / R) * (eps * R) := by
        exact mul_le_mul_of_nonneg_right hpowle (by positivity)
    _ = eps := by field_simp
