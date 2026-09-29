-- Prove2me | solution 2 for MarkovMixing.spectral_representation
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:47:21.33205+00:00
-- url     : https://prove2.me/submissions/a7d9965d-d66d-43f1-acfc-d66b42dc9d3f

import Definitions.Def_mm_spectral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  classical
  -- the symmetrising square roots
  set sq : V → ℝ := fun x => Real.sqrt (π x) with hsqdef
  have hsqpos : ∀ x : V, 0 < sq x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hsqne : ∀ x : V, sq x ≠ 0 := fun x => ne_of_gt (hsqpos x)
  have hsqsq : ∀ x : V, sq x * sq x = π x := fun x =>
    Real.mul_self_sqrt (le_of_lt (hpos x))
  -- the symmetrised matrix
  set A : Matrix V V ℝ := fun x y => sq x * P x y / sq y with hAdef
  have hAval : ∀ x y : V, A x y = sq x * P x y / sq y := fun _ _ => rfl
  have hAsymm : ∀ x y : V, A x y = A y x := by
    intro x y
    rw [hAval, hAval, div_eq_div_iff (hsqne y) (hsqne x)]
    have h1 : sq x * sq x * P x y = sq y * sq y * P y x := by
      rw [hsqsq, hsqsq]; exact hrev x y
    calc sq x * P x y * sq x = sq x * sq x * P x y := by ring
      _ = sq y * sq y * P y x := h1
      _ = sq y * P y x * sq y := by ring
  have hAh : A.IsHermitian := by
    ext x y
    rw [Matrix.conjTranspose_apply, star_trivial]
    exact hAsymm y x
  -- the eigenvector matrix
  set U : Matrix V V ℝ := (hAh.eigenvectorUnitary : Matrix V V ℝ) with hUdef
  have hUcol : ∀ j x : V, U x j = (hAh.eigenvectorBasis j) x := fun j x => rfl
  have hUstar : ∀ i j : V, (star U) i j = U j i := by
    intro i j
    rw [Matrix.star_apply, star_trivial]
  have hUU : ∀ j k : V, ∑ x, U x j * U x k = if j = k then (1 : ℝ) else 0 := by
    intro j k
    have h : (star U : Matrix V V ℝ) * U = 1 := by
      rw [hUdef]
      exact_mod_cast (Unitary.coe_star_mul_self hAh.eigenvectorUnitary)
    have h2 := congrFun (congrFun h j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun x _ => by rw [hUstar]
  have hUU' : ∀ x y : V, ∑ j, U x j * U y j = if x = y then (1 : ℝ) else 0 := by
    intro x y
    have h : U * (star U : Matrix V V ℝ) = 1 := by
      rw [hUdef]
      exact_mod_cast (Unitary.coe_mul_star_self hAh.eigenvectorUnitary)
    have h2 := congrFun (congrFun h x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by rw [hUstar]
  -- the eigenvalue equation for `A`, in coordinates
  have hAU : ∀ (j x : V), ∑ y, A x y * U y j = hAh.eigenvalues j * U x j := by
    intro j x
    have h := hAh.mulVec_eigenvectorBasis j
    have h2 := congrFun h x
    simpa [Matrix.mulVec, dotProduct, hUcol] using h2
  -- powers of `A` are the conjugated powers of `P`
  have hApow : ∀ (t : ℕ) (x y : V), (A ^ t) x y = sq x * (P ^ t) x y / sq y := by
    intro t
    induction t with
    | zero =>
        intro x y
        rw [pow_zero, pow_zero, Matrix.one_apply]
        by_cases hxy : x = y
        · rw [if_pos hxy, hxy]
          rw [mul_one, div_self (hsqne y)]
        · rw [if_neg hxy]
          simp
    | succ n ih =>
        intro x y
        have hL : (A ^ (n + 1)) x y = ∑ z, (A ^ n) x z * A z y := by
          rw [pow_succ]; rfl
        have hR : (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by
          rw [pow_succ]; rfl
        rw [hL, hR, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [ih x z, hAval]
        field_simp [hsqne z, hsqne y]
  -- transport everything to the index type `Fin (Fintype.card V)`
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with hedef
  refine ⟨fun j => hAh.eigenvalues (e j), fun j x => U x (e j) / sq x, ?_, ?_, ?_⟩
  · -- eigenfunctions of `P`
    intro j
    funext x
    have h := hAU (e j) x
    have hstep : ∑ y, P x y * (U y (e j) / sq y) = (∑ y, A x y * U y (e j)) / sq x := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hAval]
      field_simp [hsqne x, hsqne y]
    show ∑ y, P x y * (U y (e j) / sq y) = hAh.eigenvalues (e j) * (U x (e j) / sq x)
    rw [hstep, h]
    field_simp [hsqne x]
  · -- orthonormality in `ℓ²(π)`
    intro j k
    unfold innerPi
    have hterm : ∀ x : V,
        (U x (e j) / sq x) * (U x (e k) / sq x) * π x = U x (e j) * U x (e k) := by
      intro x
      rw [← hsqsq x]
      field_simp [hsqne x]
    rw [Finset.sum_congr rfl fun x _ => hterm x, hUU (e j) (e k)]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (by rw [hjk])]
    · rw [if_neg hjk, if_neg (fun hc => hjk (e.injective hc))]
  · -- the spectral decomposition of the transition probabilities
    intro t x y
    -- first: the decomposition of `A ^ t`
    have hpowU : ∀ (t : ℕ) (j x : V),
        ∑ y, (A ^ t) x y * U y j = hAh.eigenvalues j ^ t * U x j := by
      intro t
      induction t with
      | zero =>
          intro j x
          rw [pow_zero, pow_zero, one_mul]
          rw [Finset.sum_eq_single x]
          · rw [Matrix.one_apply_eq, one_mul]
          · intro z _ hz
            rw [Matrix.one_apply_ne (Ne.symm hz), zero_mul]
          · intro hc; exact absurd (Finset.mem_univ x) hc
      | succ n ih =>
          intro j x
          have hL : ∀ z : V, (A ^ (n + 1)) x z = ∑ w, A x w * (A ^ n) w z := by
            intro z
            rw [pow_succ']
            rfl
          rw [Finset.sum_congr rfl fun z _ => by rw [hL z, Finset.sum_mul]]
          rw [Finset.sum_comm]
          have hinner : ∀ w : V, ∑ z, A x w * (A ^ n) w z * U z j
              = A x w * (hAh.eigenvalues j ^ n * U w j) := by
            intro w
            rw [← ih j w, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
          rw [Finset.sum_congr rfl fun w _ => hinner w]
          have : ∑ w, A x w * (hAh.eigenvalues j ^ n * U w j)
              = hAh.eigenvalues j ^ n * ∑ w, A x w * U w j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun w _ => by ring
          rw [this, hAU j x, pow_succ]
          ring
    have hAt : (A ^ t) x y = ∑ v : V, hAh.eigenvalues v ^ t * (U x v * U y v) := by
      have hexpand : ∑ v : V, hAh.eigenvalues v ^ t * (U x v * U y v)
          = ∑ v : V, ∑ z, U y v * ((A ^ t) x z * U z v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum, hpowU t v x]
        ring
      rw [hexpand, Finset.sum_comm]
      have hcollapse : ∀ z : V, ∑ v, U y v * ((A ^ t) x z * U z v)
          = (A ^ t) x z * (if z = y then (1 : ℝ) else 0) := by
        intro z
        rw [← hUU' z y]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [Finset.sum_congr rfl fun z _ => hcollapse z, Finset.sum_eq_single y]
      · rw [if_pos rfl, mul_one]
      · intro z _ hz
        rw [if_neg hz, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ y) hc
    -- now convert to `P`
    have hdiv : (P ^ t) x y / π y = (A ^ t) x y / (sq x * sq y) := by
      rw [hApow t x y, ← hsqsq y]
      field_simp [hsqne x, hsqne y]
    rw [hdiv, hAt]
    rw [← Equiv.sum_comp e (fun v : V => hAh.eigenvalues v ^ t * (U x v * U y v))]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hsqne x, hsqne y]
