-- Prove2me | solution 1 for RademacherSymmetrization.generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:56.097891+00:00
-- url     : https://prove2.me/submissions/9fa62f22-fed3-4782-808a-b1e258cb61e2

-- Sol generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
import Theorems.Thm_RademacherSymmetrization_gap_le_ghost
import Theorems.Thm_RademacherSymmetrization_symmetrized_le
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

open RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}



lemma sum_sign_neg (g : (Fin n → Bool) → ℝ) :
    ∑ ε : Fin n → Bool, g (fun j => !(ε j)) = ∑ ε : Fin n → Bool, g ε := by
  refine Finset.sum_nbij' (fun ε => fun j => !(ε j)) (fun ε => fun j => !(ε j))
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp








/-! ### The product measure -/

omit [Fintype X] [DecidableEq X] in
lemma wt_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (S : Fin n → X) : 0 ≤ wt p S :=
  Finset.prod_nonneg fun i _ => hp (S i)

omit [DecidableEq X] in
lemma sum_wt {p : X → ℝ} (hp1 : ∑ x, p x = 1) : ∑ S : Fin n → X, wt p S = 1 := by
  classical
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => X)
      (fun _ => (Finset.univ : Finset X)) (fun _ x => p x)
  rw [Fintype.piFinset_univ] at h
  unfold wt
  rw [← h, hp1, Finset.prod_const_one]



/-! ### Step 1: introducing the ghost sample -/



/-! ### Step 2: the swapping involution -/


omit [Fintype X] [DecidableEq X] in
lemma swapPair_involutive (ε : Fin n → Bool) :
    Function.Involutive (swapPair (X := X) ε) := by
  intro q
  ext i <;> by_cases h : ε i = true <;> simp [swapPair, h]

omit [Fintype X] [DecidableEq X] in
lemma wt_swapPair {p : X → ℝ} (ε : Fin n → Bool) (q : (Fin n → X) × (Fin n → X)) :
    wt p (swapPair ε q).1 * wt p (swapPair ε q).2 = wt p q.1 * wt p q.2 := by
  unfold wt swapPair
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : ε i = true <;> simp [h, mul_comm]

omit [Fintype X] [DecidableEq X] in
lemma ghostGap_swapPair (F : Finset (X → ℝ)) (hne : F.Nonempty)
    (ε : Fin n → Bool) (q : (Fin n → X) × (Fin n → X)) :
    ghostGap F hne (swapPair ε q).1 (swapPair ε q).2
      = F.sup' hne (fun f => (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i))) := by
  unfold ghostGap
  refine Finset.sup'_congr hne rfl fun f _ => ?_
  unfold emp swapPair
  simp only
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i = true <;> simp [sgn, h]

/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/


/-! ### A Massart bound for the empirical Rademacher complexity of a finite class

To turn the symmetrization inequality into a concrete generalization bound we bound the
empirical Rademacher complexity of a finite class of uniformly bounded functions by the
Chernoff/moment generating function argument, exactly as in Massart's finite class
lemma.
-/









open RademacherSymmetrization in
omit [DecidableEq X] in
theorem solution{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hn : 0 < n) (F : Finset (X → ℝ)) (hne : F.Nonempty) :
    ∑ S : Fin n → X, wt p S * gap F hne p S
      ≤ 2 * ∑ S : Fin n → X, wt p S * radS F hne S := by
  classical
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  set G : (Fin n → X) × (Fin n → X) → ℝ :=
    fun q => wt p q.1 * wt p q.2 * ghostGap F hne q.1 q.2 with hG
  set K : (Fin n → Bool) → ℝ := fun ε =>
    ∑ q : (Fin n → X) × (Fin n → X), wt p q.1 * wt p q.2 *
      F.sup' hne (fun f => (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i))) with hK
  -- Step 1: compare with the ghost sample
  have step1 : ∑ S : Fin n → X, wt p S * gap F hne p S
      ≤ ∑ q : (Fin n → X) × (Fin n → X), G q := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun S _ => ?_
    have h := gap_le_ghost hp hp1 hn F hne S
    calc wt p S * gap F hne p S
        ≤ wt p S * ∑ S' : Fin n → X, wt p S' * ghostGap F hne S S' :=
          mul_le_mul_of_nonneg_left h (wt_nonneg hp S)
      _ = ∑ S' : Fin n → X, G (S, S') := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S' _ => ?_
          simp only [hG]
          ring
  -- Step 2: for each sign pattern the swap is a weight preserving involution
  have step2 : ∀ ε : Fin n → Bool, ∑ q : (Fin n → X) × (Fin n → X), G q = K ε := by
    intro ε
    have hperm := Equiv.sum_comp (swapPair_involutive (X := X) ε).toPerm G
    rw [← hperm]
    refine Finset.sum_congr rfl fun q _ => ?_
    show G (swapPair ε q) = _
    simp only [hG]
    rw [wt_swapPair ε q, ghostGap_swapPair F hne ε q]
  -- Step 3: split the symmetrized term into two Rademacher terms
  have step3 : ∀ ε : Fin n → Bool, K ε
      ≤ ∑ S : Fin n → X, wt p S * maxCorr F hne ε S
        + ∑ S : Fin n → X, wt p S * maxCorr F hne (fun j => !(ε j)) S := by
    intro ε
    have hle : K ε ≤ ∑ q : (Fin n → X) × (Fin n → X), wt p q.1 * wt p q.2 *
        (maxCorr F hne ε q.2 + maxCorr F hne (fun j => !(ε j)) q.1) := by
      simp only [hK]
      refine Finset.sum_le_sum fun q _ => ?_
      exact mul_le_mul_of_nonneg_left (symmetrized_le F hne ε q)
        (mul_nonneg (wt_nonneg hp q.1) (wt_nonneg hp q.2))
    refine hle.trans (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ S : Fin n → X, (∑ S' : Fin n → X, wt p S * wt p S' *
        (maxCorr F hne ε S' + maxCorr F hne (fun j => !(ε j)) S))
        = wt p S * (∑ S' : Fin n → X, wt p S' * maxCorr F hne ε S')
          + wt p S * maxCorr F hne (fun j => !(ε j)) S := by
      intro S
      have h1 : ∀ S' : Fin n → X, wt p S * wt p S' *
          (maxCorr F hne ε S' + maxCorr F hne (fun j => !(ε j)) S)
          = wt p S * (wt p S' * maxCorr F hne ε S')
            + (wt p S * maxCorr F hne (fun j => !(ε j)) S) * wt p S' := fun S' => by ring
      rw [Finset.sum_congr rfl fun S' _ => h1 S', Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, sum_wt hp1, mul_one]
    rw [Finset.sum_congr rfl fun S _ => hsplit S, Finset.sum_add_distrib,
      ← Finset.sum_mul, sum_wt hp1, one_mul]
  -- averaging the identity of Step 2 over all sign patterns
  have hconst : ∑ ε : Fin n → Bool, K ε
      = 2 ^ n * ∑ q : (Fin n → X) × (Fin n → X), G q := by
    rw [Finset.sum_congr rfl fun ε _ => (step2 ε).symm, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    ring
  have hswap : ∑ ε : Fin n → Bool, ∑ S : Fin n → X,
        wt p S * maxCorr F hne (fun j => !(ε j)) S
      = ∑ ε : Fin n → Bool, ∑ S : Fin n → X, wt p S * maxCorr F hne ε S :=
    sum_sign_neg (fun ε => ∑ S : Fin n → X, wt p S * maxCorr F hne ε S)
  have hradsum : ∑ ε : Fin n → Bool, ∑ S : Fin n → X, wt p S * maxCorr F hne ε S
      = 2 ^ n * ∑ S : Fin n → X, wt p S * radS F hne S := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold radS
    rw [← Finset.mul_sum]
    field_simp
  have hsum : ∑ ε : Fin n → Bool, K ε
      ≤ 2 * (2 ^ n * ∑ S : Fin n → X, wt p S * radS F hne S) := by
    calc ∑ ε : Fin n → Bool, K ε
        ≤ ∑ ε : Fin n → Bool, (∑ S : Fin n → X, wt p S * maxCorr F hne ε S
            + ∑ S : Fin n → X, wt p S * maxCorr F hne (fun j => !(ε j)) S) :=
          Finset.sum_le_sum fun ε _ => step3 ε
      _ = 2 * (2 ^ n * ∑ S : Fin n → X, wt p S * radS F hne S) := by
          rw [Finset.sum_add_distrib, hswap, hradsum]
          ring
  have hGle : ∑ q : (Fin n → X) × (Fin n → X), G q
      ≤ 2 * ∑ S : Fin n → X, wt p S * radS F hne S := by
    have h1 : 2 ^ n * ∑ q : (Fin n → X) × (Fin n → X), G q
        ≤ 2 ^ n * (2 * ∑ S : Fin n → X, wt p S * radS F hne S) := by
      rw [← hconst]
      calc ∑ ε : Fin n → Bool, K ε
          ≤ 2 * (2 ^ n * ∑ S : Fin n → X, wt p S * radS F hne S) := hsum
        _ = 2 ^ n * (2 * ∑ S : Fin n → X, wt p S * radS F hne S) := by ring
    exact le_of_mul_le_mul_left h1 hpow
  exact step1.trans hGle
