-- Prove2me | solution 2 for TropicalLA.charCoeff_card_eq_tdet
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:36:12.552642+00:00
-- url     : https://prove2.me/submissions/9618a8ef-029e-4311-bb9b-804dfd257060

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean ====
/-
# The max-plus (tropical) semiring

We construct the tropical semiring `(R ∪ {-∞}, max, +)` as a type synonym
`MaxPlus R := WithBot R` for a linearly ordered additive commutative monoid `R`
(the motivating case being `R = ℝ`), equip it with a `CommSemiring` structure,
and record its characteristic tropical features:

* it is **idempotent**: `a + a = a`;
* it is **zero-sum-free**: `a + b = 0 → a = 0 ∧ b = 0`, so (for nontrivial `R`)
  it admits no additive inverses and is genuinely not a ring;
* finite tropical sums are suprema (`toBot_sum`);
* consequently tropical matrix multiplication is the `max`-of-sums formula and
  is associative.
-/

namespace TropicalLA

-- [dropped: platform already declares MaxPlus]
namespace MaxPlus

-- [dropped: platform already declares ofBot]
-- [dropped: platform already declares toBot]
@[simp] theorem toBot_ofBot {R : Type*} (x : WithBot R) : toBot (ofBot x) = x := rfl
@[simp] theorem ofBot_toBot {R : Type*} (x : MaxPlus R) : ofBot (toBot x) = x := rfl

-- [dropped: platform already declares ofBot_injective]
/-- Tropical addition is `max`. -/
instance {R : Type*} [LinearOrder R] : Add (MaxPlus R) :=
  ⟨fun a b => ofBot (max (toBot a) (toBot b))⟩
/-- Tropical multiplication is ordinary addition. -/
instance {R : Type*} [Add R] : Mul (MaxPlus R) := ⟨fun a b => ofBot (toBot a + toBot b)⟩

@[simp] theorem toBot_add {R : Type*} [LinearOrder R] (a b : MaxPlus R) :
    toBot (a + b) = max (toBot a) (toBot b) := rfl
@[simp] theorem toBot_mul {R : Type*} [Add R] (a b : MaxPlus R) :
    toBot (a * b) = toBot a + toBot b := rfl
@[simp] theorem toBot_zero {R : Type*} : toBot (0 : MaxPlus R) = ⊥ := rfl
@[simp] theorem toBot_one {R : Type*} [Zero R] :
    toBot (1 : MaxPlus R) = ((0 : R) : WithBot R) := rfl

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]

instance : CommSemiring (MaxPlus R) where
  add_assoc a b c := congrArg ofBot (max_assoc _ _ _)
  zero_add a := congrArg ofBot (max_eq_right bot_le)
  add_zero a := congrArg ofBot (max_eq_left bot_le)
  add_comm a b := congrArg ofBot (max_comm _ _)
  mul_assoc a b c := congrArg ofBot (add_assoc _ _ _)
  one_mul a := congrArg ofBot (zero_add (toBot a))
  mul_one a := congrArg ofBot (add_zero (toBot a))
  mul_comm a b := congrArg ofBot (add_comm _ _)
  left_distrib a b c := congrArg ofBot (add_max (toBot a) (toBot b) (toBot c))
  right_distrib a b c := congrArg ofBot (max_add (toBot a) (toBot b) (toBot c))
  zero_mul a := congrArg ofBot (WithBot.bot_add (toBot a))
  mul_zero a := congrArg ofBot (WithBot.add_bot (toBot a))
  nsmul := nsmulRec

/-- Tropical addition is idempotent: the max-plus semiring is an *idempotent* semiring. -/
@[simp] theorem add_self {R : Type*} [LinearOrder R] (a : MaxPlus R) : a + a = a :=
  congrArg ofBot (max_self _)

/-- The tropical order: `a ≤ b` iff `a + b = b`. -/
theorem add_eq_right_iff_le {R : Type*} [LinearOrder R] (a b : MaxPlus R) :
    a + b = b ↔ toBot a ≤ toBot b := by
  constructor
  · intro h
    have h' : max (toBot a) (toBot b) = toBot b := congrArg toBot h
    exact h' ▸ le_max_left (toBot a) (toBot b)
  · intro h
    exact congrArg ofBot (max_eq_right h)

/-- The max-plus semiring is **zero-sum-free**: a tropical sum vanishes only if both
summands do.  In particular no nonzero element has an additive inverse. -/
theorem eq_zero_of_add_eq_zero {R : Type*} [LinearOrder R] {a b : MaxPlus R} (h : a + b = 0) :
    a = 0 ∧ b = 0 := by
  have h' : max (toBot a) (toBot b) = ⊥ := congrArg toBot h
  refine ⟨ofBot_injective ?_, ofBot_injective ?_⟩
  · exact le_bot_iff.mp (h' ▸ le_max_left (toBot a) (toBot b))
  · exact le_bot_iff.mp (h' ▸ le_max_right (toBot a) (toBot b))

/-- Since the semiring is zero-sum-free and nontrivial, it is not a ring:
`1` has no additive inverse. -/
theorem no_neg_one {R : Type*} [Zero R] [LinearOrder R] : ¬ ∃ b : MaxPlus R, (1 : MaxPlus R) + b = 0 := by
  rintro ⟨b, hb⟩
  have h1 : (1 : MaxPlus R) = 0 := (eq_zero_of_add_eq_zero hb).1
  have h2 : ((0 : R) : WithBot R) = (⊥ : WithBot R) := congrArg toBot h1
  exact WithBot.coe_ne_bot h2

/-- A finite tropical sum is the supremum of its terms. -/
theorem toBot_sum {ι : Type*} (s : Finset ι) (f : ι → MaxPlus R) :
    toBot (∑ i ∈ s, f i) = s.sup (fun i => toBot (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sup_insert, toBot_add, ih]

/-- A finite tropical product is the sum of its terms. -/
theorem toBot_prod {ι : Type*} (s : Finset ι) (f : ι → MaxPlus R) :
    toBot (∏ i ∈ s, f i) = ∑ i ∈ s, toBot (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, toBot_mul, ih]

section Matrices

variable {ι : Type*} [Fintype ι]

/-- The entries of a tropical matrix product: `(A ⊗ B) i j = max_k (A i k + B k j)`,
where `max` and `+` are taken in `R ∪ {-∞}`. -/
theorem toBot_matrix_mul (A B : Matrix ι ι (MaxPlus R)) (i j : ι) :
    toBot ((A * B) i j) = Finset.univ.sup (fun k => toBot (A i k) + toBot (B k j)) := by
  rw [Matrix.mul_apply, toBot_sum]
  simp

/-- **Tropical matrix multiplication is associative.** -/
theorem matrix_mul_assoc (A B C : Matrix ι ι (MaxPlus R)) : A * B * C = A * (B * C) :=
  Matrix.mul_assoc A B C

end Matrices

end MaxPlus

end TropicalLA
-- ==== upstream: Packages/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean ====
/-
# Tropical (max-plus) matrices with finite entries

For matrices with entries in `ℝ` (i.e. no `-∞` entries) tropical multiplication is

  `(A ⊗ B) i j = max_k (A i k + B k j)`,

implemented with `Finset.sup'`.  We prove

* `tmul_assoc` : tropical matrix multiplication is associative (a hands-on proof,
  independent of the semiring instance);
* `tmul_embed`  : this operation agrees with multiplication in `Matrix ι ι (MaxPlus ℝ)`,
  so the two developments are coherent;
* `tpow_isGreatest` : **max-plus powers compute optimal paths** — the `(i,j)` entry of
  `A^{⊗(m+1)}` is the maximal weight of a length-`(m+1)` walk from `i` to `j`
  (the algebraic form of the Bellman dynamic-programming principle).
-/


namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- [dropped: platform already declares tmul]
-- [dropped: platform already declares tmulVec]
theorem le_tmul (A B : Matrix ι ι ℝ) (i j k : ι) : A i k + B k j ≤ tmul A B i j :=
  Finset.le_sup' (fun k => A i k + B k j) (Finset.mem_univ k)

theorem tmul_le {A B : Matrix ι ι ℝ} {i j : ι} {c : ℝ} (h : ∀ k, A i k + B k j ≤ c) :
    tmul A B i j ≤ c := Finset.sup'_le _ _ fun k _ => h k

theorem exists_tmul_eq (A B : Matrix ι ι ℝ) (i j : ι) : ∃ k, tmul A B i j = A i k + B k j := by
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun k => A i k + B k j)
  exact ⟨k, hk⟩

theorem le_tmulVec (A : Matrix ι ι ℝ) (v : ι → ℝ) (i j : ι) : A i j + v j ≤ tmulVec A v i :=
  Finset.le_sup' (fun j => A i j + v j) (Finset.mem_univ j)

-- [dropped: platform already declares exists_tmulVec_eq]
/-- **Associativity of tropical matrix multiplication**, proved directly from the
`max`-of-sums formula. -/
theorem tmul_assoc (A B C : Matrix ι ι ℝ) : tmul (tmul A B) C = tmul A (tmul B C) := by
  funext i j
  apply le_antisymm
  · refine tmul_le fun k => ?_
    obtain ⟨l, hl⟩ := exists_tmul_eq A B i k
    have h1 := le_tmul B C l j k
    have h2 := le_tmul A (tmul B C) i j l
    rw [hl]; linarith
  · refine tmul_le fun l => ?_
    obtain ⟨k, hk⟩ := exists_tmul_eq B C l j
    have h1 := le_tmul A B i k l
    have h2 := le_tmul (tmul A B) C i j k
    rw [hk]; linarith

/-- Tropical multiplication distributes over the entrywise `max` of matrices. -/
theorem tmul_add_distrib (A B C : Matrix ι ι ℝ) (i j : ι) :
    tmul A (fun i j => max (B i j) (C i j)) i j = max (tmul A B i j) (tmul A C i j) := by
  apply le_antisymm
  · refine tmul_le fun k => ?_
    show A i k + max (B k j) (C k j) ≤ _
    rcases le_total (B k j) (C k j) with h | h
    · rw [max_eq_right h]
      exact le_trans (le_tmul A C i j k) (le_max_right _ _)
    · rw [max_eq_left h]
      exact le_trans (le_tmul A B i j k) (le_max_left _ _)
  · refine max_le (tmul_le fun k => ?_) (tmul_le fun k => ?_)
    · have h1 := le_tmul A (fun i j => max (B i j) (C i j)) i j k
      have h2 := le_max_left (B k j) (C k j)
      simp only at h1
      linarith
    · have h1 := le_tmul A (fun i j => max (B i j) (C i j)) i j k
      have h2 := le_max_right (B k j) (C k j)
      simp only at h1
      linarith

section Embedding

-- [dropped: platform already declares embed]
theorem coe_sup' {κ : Type*} {s : Finset κ} (H : s.Nonempty) (f : κ → ℝ) :
    ((s.sup' H f : ℝ) : WithBot ℝ) = s.sup (fun i => ((f i : ℝ) : WithBot ℝ)) := by
  obtain ⟨k, hk, hks⟩ := Finset.exists_mem_eq_sup' H f
  apply le_antisymm
  · rw [hks]; exact Finset.le_sup (f := fun i => ((f i : ℝ) : WithBot ℝ)) hk
  · refine Finset.sup_le fun i hi => ?_
    exact_mod_cast Finset.le_sup' f hi

/-- **Coherence**: the hands-on `max`-of-sums product agrees with the semiring
matrix product in `Matrix ι ι (MaxPlus ℝ)`. -/
theorem tmul_embed (A B : Matrix ι ι ℝ) (i j : ι) :
    MaxPlus.toBot ((embed A * embed B) i j) = ((tmul A B i j : ℝ) : WithBot ℝ) := by
  rw [MaxPlus.toBot_matrix_mul, tmul, coe_sup']
  refine Finset.sup_congr rfl fun k _ => ?_
  simp [embed]

end Embedding

section Paths

-- [dropped: platform already declares tpow]
-- [dropped: platform already declares pathWeight]
/-- **Tropical powers compute maximum-weight walks.**  The `(i,j)` entry of the
`(m+1)`-st tropical power of `A` is the greatest weight of a walk of length `m+1`
from `i` to `j`; in particular that optimum is attained. -/
theorem tpow_isGreatest (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    IsGreatest {w : ℝ | ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = j ∧ w = pathWeight A p (m + 1)}
      (tpow A m i j) := by
  induction m generalizing i j with
  | zero =>
      constructor
      · refine ⟨fun t => if t = 0 then i else j, by simp, by simp, ?_⟩
        simp [pathWeight, tpow]
      · rintro w ⟨p, hp0, hp1, rfl⟩
        simp [pathWeight, hp0, hp1, tpow]
  | succ m ih =>
      constructor
      · obtain ⟨k, hk⟩ := exists_tmul_eq (tpow A m) A i j
        obtain ⟨p, hp0, hpm, hpw⟩ := (ih i k).1
        refine ⟨fun t => if t ≤ m + 1 then p t else j, by simpa using hp0, by simp, ?_⟩
        have hsum : ∑ t ∈ Finset.range (m + 1),
            A ((fun t => if t ≤ m + 1 then p t else j) t)
              ((fun t => if t ≤ m + 1 then p t else j) (t + 1)) = pathWeight A p (m + 1) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [Finset.mem_range] at ht
          have h1 : t ≤ m + 1 := by omega
          have h2 : t + 1 ≤ m + 1 := by omega
          simp [h1, h2]
        show tpow A (m + 1) i j = pathWeight A _ (m + 2)
        rw [pathWeight, Finset.sum_range_succ, hsum]
        have hlt : ¬ (m + 2 ≤ m + 1) := by omega
        simp only [hlt, if_false, le_refl, if_true]
        rw [hpm] at *
        show tmul (tpow A m) A i j = _
        rw [hk, ← hpw]
      · rintro w ⟨p, hp0, hpm, rfl⟩
        rw [pathWeight, Finset.sum_range_succ]
        have h1 : ∑ t ∈ Finset.range (m + 1), A (p t) (p (t + 1)) ≤ tpow A m i (p (m + 1)) :=
          (ih i (p (m + 1))).2 ⟨p, hp0, rfl, rfl⟩
        have h2 : tpow A m i (p (m + 1)) + A (p (m + 1)) j ≤ tmul (tpow A m) A i j :=
          le_tmul (tpow A m) A i j (p (m + 1))
        have h3 : A (p (m + 1)) (p (m + 2)) = A (p (m + 1)) j := by rw [hpm]
        show _ ≤ tmul (tpow A m) A i j
        rw [h3]
        linarith

end Paths

end TropicalLA
-- ==== upstream: Packages/Catalog/Algebra/TropicalLinearAlgebra/TropicalDeterminant.lean ====
/-
# The tropical determinant

Over the max-plus semiring the determinant of `A` (there being no signs) is

  `tdet A = max_{σ ∈ S_ι} Σ_i A i (σ i)`,

i.e. the value of the **optimal assignment problem** for the weight matrix `A`.

Main results:

* `tdet_isGreatest` : the tropical determinant *is* the weight of a maximum-weight
  permutation, and that maximum is attained;
* `tdet_transpose`  : invariance under transposition;
* `tdet_tmul_ge`    : **supermultiplicativity** `tdet A + tdet B ≤ tdet (A ⊗ B)`
  (the tropical Cauchy–Binet inequality); equality can fail — see
  `TropicalLA.Examples.tdet_tmul_strict` in `Examples.lean`;
* `tdet_diag_le` and `tdet_eq_trace_of_diagonally_dominant` : the diagonal always
  gives a lower bound, with equality under a Monge-type dominance condition.
-/


namespace TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- [dropped: platform already declares permWeight]
-- [dropped: platform already declares tdet]
theorem permWeight_le_tdet (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) : permWeight A σ ≤ tdet A :=
  Finset.le_sup' (permWeight A) (Finset.mem_univ σ)

theorem exists_permWeight_eq_tdet (A : Matrix ι ι ℝ) : ∃ σ, tdet A = permWeight A σ := by
  obtain ⟨σ, _, hσ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Equiv.Perm ι)) (permWeight A)
  exact ⟨σ, hσ⟩

/-- **The tropical determinant is the weight of a maximum-weight permutation.** -/
theorem tdet_isGreatest (A : Matrix ι ι ℝ) :
    IsGreatest {w : ℝ | ∃ σ : Equiv.Perm ι, w = permWeight A σ} (tdet A) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_permWeight_eq_tdet A
    exact ⟨σ, hσ⟩
  · rintro w ⟨σ, rfl⟩
    exact permWeight_le_tdet A σ

/-- The determinant is unchanged by transposition: `σ ↦ σ⁻¹` matches the two families. -/
theorem tdet_transpose (A : Matrix ι ι ℝ) : tdet A.transpose = tdet A := by
  have key : ∀ (B : Matrix ι ι ℝ), tdet B.transpose ≤ tdet B := by
    intro B
    refine Finset.sup'_le _ _ fun σ _ => ?_
    have : permWeight B.transpose σ = permWeight B σ⁻¹ := by
      unfold permWeight
      rw [← Equiv.sum_comp σ (fun j => B j (σ⁻¹ j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.transpose_apply]
    rw [this]
    exact permWeight_le_tdet B σ⁻¹
  refine le_antisymm (key A) ?_
  simpa using key A.transpose

/-- **Tropical supermultiplicativity (Cauchy–Binet inequality)**:
`tdet A + tdet B ≤ tdet (A ⊗ B)`.

The proof composes an optimal permutation for `A` with one for `B`: the product
matrix contains at least the composite assignment as one of its choices. -/
theorem tdet_tmul_ge [Nonempty ι] (A B : Matrix ι ι ℝ) : tdet A + tdet B ≤ tdet (tmul A B) := by
  obtain ⟨σ, hσ⟩ := exists_permWeight_eq_tdet A
  obtain ⟨τ, hτ⟩ := exists_permWeight_eq_tdet B
  have hB : permWeight B τ = ∑ i, B (σ i) (τ (σ i)) := by
    unfold permWeight
    rw [← Equiv.sum_comp σ (fun j => B j (τ j))]
  have hkey : permWeight A σ + permWeight B τ ≤ permWeight (tmul A B) (σ.trans τ) := by
    rw [hB]
    simp only [permWeight, Equiv.trans_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => le_tmul A B i (τ (σ i)) (σ i)
  rw [hσ, hτ]
  exact le_trans hkey (permWeight_le_tdet _ _)

/-- Reindexing: the weights of `A` along permutations are exactly the sums used above,
so the identity permutation gives the trace bound. -/
theorem tdet_diag_le (A : Matrix ι ι ℝ) : ∑ i, A i i ≤ tdet A :=
  permWeight_le_tdet A 1

/-- If every off-diagonal entry is dominated by the corresponding diagonal entry
in the strong (row-wise) sense `A i j ≤ A i i` for all `j`, then the tropical
determinant is the tropical trace `Σ_i A i i`. -/
theorem tdet_eq_diag_of_dominant (A : Matrix ι ι ℝ) (h : ∀ i j, A i j ≤ A i i) :
    tdet A = ∑ i, A i i := by
  refine le_antisymm (Finset.sup'_le _ _ fun σ _ => ?_) (tdet_diag_le A)
  exact Finset.sum_le_sum fun i _ => h i (σ i)

end TropicalLA
-- ==== upstream: Packages/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean ====
/-
# Tropical eigenvalues and the max-plus Perron–Frobenius theorem

An eigenpair of a max-plus matrix `A` (finite real entries) is a pair `(lam, v)`
with `A ⊗ v = lam ⊗ v`, i.e.

  `max_j (A i j + v j) = lam + v i`  for every `i`.

Main results of this file:

* `IsTropEigen.cycle_le` : every closed walk (cycle) of `A` has weight at most
  `length · lam` — an eigenvalue dominates all cycle means;
* `IsTropEigen.exists_critical_cycle` : some *simple* cycle attains the mean `lam`
  exactly (the critical cycle), obtained from the argmax function of the eigenvector
  by a minimal-period pigeonhole argument;
* `IsTropEigen.isGreatest_cycleMean` : **tropical Perron–Frobenius (spectral part)** —
  `lam` is the *maximum cycle mean* of `A`, and hence
* `tropEigenvalue_unique` : a max-plus matrix has at most one eigenvalue.
-/


namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- [dropped: platform already declares IsTropEigen]
namespace IsTropEigen

variable {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}

/-- The eigenvector inequality `A i j + v j ≤ lam + v i`. -/
theorem le_of (h : IsTropEigen A lam v) (i j : ι) : A i j + v j ≤ lam + v i := by
  rw [← h i]; exact le_tmulVec A v i j

-- [dropped: platform already declares exists_tight]
/-- **Every cycle mean is at most the eigenvalue.**  For a closed walk
`c 0 → c 1 → ⋯ → c m = c 0` the total weight is at most `m · lam`; the eigenvector
values telescope away. -/
theorem cycle_le (h : IsTropEigen A lam v) {m : ℕ} {c : ℕ → ι} (hc : c m = c 0) :
    pathWeight A c m ≤ m * lam := by
  have step : ∀ t ∈ Finset.range m,
      A (c t) (c (t + 1)) ≤ lam + ((fun t => v (c t)) t - (fun t => v (c t)) (t + 1)) := by
    intro t _
    have := h.le_of (c t) (c (t + 1))
    simp only
    linarith
  have hsum := Finset.sum_le_sum step
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun t => v (c t)) m] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [pathWeight]
  simp only [hc] at hsum
  linarith

/-- The mean weight of any cycle is at most the eigenvalue. -/
theorem cycleMean_le (h : IsTropEigen A lam v) {m : ℕ} (hm : 1 ≤ m) {c : ℕ → ι}
    (hc : c m = c 0) : pathWeight A c m / m ≤ lam := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  have := h.cycle_le hc
  linarith [this]

section CriticalCycle

-- [dropped: platform already declares exists_minimal_periodic_point]
/-- Points on the minimal-period orbit are pairwise distinct. -/
theorem iterate_injOn_of_minimal_period {f : ι → ι} {y : ι} {p : ℕ}
    (hp : f^[p] y = y) (hmin : ∀ q, 0 < q → q < p → f^[q] y ≠ y) :
    Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) := by
  intro s hs t ht hst
  simp only [Finset.coe_range, Set.mem_Iio] at hs ht
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : f^[p - t + s] y = y := by
      rw [Function.iterate_add_apply]
      simp only at hst
      rw [hst, ← Function.iterate_add_apply]
      have : p - t + t = p := by omega
      rw [this, hp]
    exact hmin (p - t + s) (by omega) (by omega) this
  · have : f^[p - s + t] y = y := by
      rw [Function.iterate_add_apply]
      simp only at hst
      rw [← hst, ← Function.iterate_add_apply]
      have : p - s + s = p := by omega
      rw [this, hp]
    exact hmin (p - s + t) (by omega) (by omega) this

/-- **Existence of a critical cycle.**  If `lam` is an eigenvalue, some closed walk
has mean weight exactly `lam`; moreover it can be taken *simple*: its `p` vertices
`y, f y, …, f^{p-1} y` are pairwise distinct. -/
theorem exists_critical_cycle (h : IsTropEigen A lam v) :
    ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
      Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) ∧
      (∀ i, A i (f i) + v (f i) = lam + v i) ∧
      pathWeight A (fun t => f^[t] y) p = p * lam := by
  obtain ⟨f, y, p, hp0, hp, hmin, hf⟩ := h.exists_minimal_periodic_point
  refine ⟨f, y, p, hp0, hp, iterate_injOn_of_minimal_period hp hmin, hf, ?_⟩
  have hterm : ∀ t : ℕ, A (f^[t] y) (f^[t + 1] y) =
      lam + ((fun t => v (f^[t] y)) t - (fun t => v (f^[t] y)) (t + 1)) := by
    intro t
    have h1 := hf (f^[t] y)
    have h2 : f^[t + 1] y = f (f^[t] y) := by
      rw [Function.iterate_succ_apply']
    rw [h2]
    simp only
    rw [h2]
    linarith
  rw [pathWeight]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun t => v (f^[t] y)) p]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Function.iterate_zero_apply, hp]
  ring

end CriticalCycle

/-- **Tropical Perron–Frobenius, spectral part.**  An eigenvalue of a max-plus matrix
is exactly the *maximum cycle mean*: it dominates every cycle mean and is attained by
some cycle. -/
theorem isGreatest_cycleMean (h : IsTropEigen A lam v) :
    IsGreatest {μ : ℝ | ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ c m = c 0 ∧ μ = pathWeight A c m / m}
      lam := by
  constructor
  · obtain ⟨f, y, p, hp0, hp, _, _, hw⟩ := h.exists_critical_cycle
    refine ⟨p, fun t => f^[t] y, hp0, by simpa using hp, ?_⟩
    rw [hw]
    have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  · rintro μ ⟨m, c, hm, hc, rfl⟩
    exact h.cycleMean_le hm hc

end IsTropEigen

/-- **Uniqueness of the tropical eigenvalue.**  Any two eigenvalues of the same
max-plus matrix coincide — both equal the maximum cycle mean. -/
theorem tropEigenvalue_unique {A : Matrix ι ι ℝ} {lam₁ lam₂ : ℝ} {v₁ v₂ : ι → ℝ}
    (h₁ : IsTropEigen A lam₁ v₁) (h₂ : IsTropEigen A lam₂ v₂) : lam₁ = lam₂ := by
  have key : ∀ {a b : ℝ} {w₁ w₂ : ι → ℝ}, IsTropEigen A a w₁ → IsTropEigen A b w₂ → a ≤ b := by
    intro a b w₁ w₂ ha hb
    obtain ⟨f, y, p, hp0, hp, _, _, hw⟩ := ha.exists_critical_cycle
    have hle := hb.cycle_le (c := fun t => f^[t] y) (m := p) (by simpa using hp)
    rw [hw] at hle
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
    nlinarith
  exact le_antisymm (key h₁ h₂) (key h₂ h₁)

end TropicalLA
-- ==== upstream: Packages/Catalog/Algebra/TropicalLinearAlgebra/TropicalCharPoly.lean ====
/-
# The tropical characteristic polynomial and its roots

For a max-plus matrix `A` on an `n`-element index set the tropical characteristic
polynomial is

  `p_A(x) = max_{0 ≤ k ≤ n} ( c_k + (n - k)·x )`,   `c_k = max_{|s| = k, σ(s) = s} Σ_{i ∈ s} A i (σ i)`,

the coefficient `c_k` being the tropical determinant of the best principal `k × k`
minor (`charCoeff`).  A point `x` is a **tropical root** when the maximum defining
`p_A(x)` is attained at two different degrees `k` (the standard corner-locus
definition of a root of a tropical polynomial).

Main results:

* `charCoeff_card_eq_tdet` : the top coefficient is the tropical determinant;
* `charCoeff_le_of_eigen`  : if `lam` is an eigenvalue then `c_k ≤ k·lam` for all `k`;
* `exists_charCoeff_eq_of_eigen` : equality `c_k = k·lam` holds for some `1 ≤ k ≤ n`,
  witnessed by the critical cycle turned into a genuine permutation;
* `eigen_isTropicalRoot` : **every tropical eigenvalue is a root of the tropical
  characteristic polynomial**, with the maximum attained both at degree `0` and at
  the length of a critical cycle, and `p_A(lam) = n·lam`.
-/


namespace TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- [dropped: platform already declares minorWeight]
-- [dropped: platform already declares admPairs]
theorem mem_admPairs {k : ℕ} {s : Finset ι} {σ : Equiv.Perm ι} :
    (s, σ) ∈ admPairs ι k ↔ s.card = k ∧ ∀ i ∈ s, σ i ∈ s := by
  simp [admPairs]

theorem admPairs_nonempty {k : ℕ} (hk : k ≤ Fintype.card ι) : (admPairs ι k).Nonempty := by
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := k) (by simpa using hk)
  exact ⟨(s, 1), mem_admPairs.mpr ⟨hs, fun i hi => by simpa using hi⟩⟩

-- [dropped: platform already declares charCoeff]
theorem le_charCoeff (A : Matrix ι ι ℝ) {k : ℕ} {s : Finset ι} {σ : Equiv.Perm ι}
    (hp : (s, σ) ∈ admPairs ι k) : minorWeight A s σ ≤ charCoeff A k := by
  have hne : (admPairs ι k).Nonempty := ⟨(s, σ), hp⟩
  rw [charCoeff, dif_pos hne]
  exact Finset.le_sup' (fun p => minorWeight A p.1 p.2) hp

theorem charCoeff_le (A : Matrix ι ι ℝ) {k : ℕ} {c : ℝ} (hne : (admPairs ι k).Nonempty)
    (h : ∀ p ∈ admPairs ι k, minorWeight A p.1 p.2 ≤ c) : charCoeff A k ≤ c := by
  rw [charCoeff, dif_pos hne]
  exact Finset.sup'_le _ _ h

/-- Degree-`0` coefficient: the empty minor has weight `0`. -/
@[simp] theorem charCoeff_zero (A : Matrix ι ι ℝ) : charCoeff A 0 = 0 := by
  have hne : (admPairs ι 0).Nonempty :=
    ⟨(∅, 1), mem_admPairs.mpr ⟨by simp, by simp⟩⟩
  refine le_antisymm (charCoeff_le A hne ?_) ?_
  · rintro ⟨s, σ⟩ hp
    rw [mem_admPairs] at hp
    have : s = ∅ := Finset.card_eq_zero.mp hp.1
    simp [minorWeight, this]
  · have hmem : ((∅ : Finset ι), (1 : Equiv.Perm ι)) ∈ admPairs ι 0 :=
      mem_admPairs.mpr ⟨by simp, by simp⟩
    simpa [minorWeight] using le_charCoeff A hmem

/-- The top coefficient of the tropical characteristic polynomial is the tropical
determinant. -/
theorem charCoeff_card_eq_tdet (A : Matrix ι ι ℝ) :
    charCoeff A (Fintype.card ι) = tdet A := by
  have hne : (admPairs ι (Fintype.card ι)).Nonempty := admPairs_nonempty le_rfl
  refine le_antisymm (charCoeff_le A hne ?_) ?_
  · rintro ⟨s, σ⟩ hp
    rw [mem_admPairs] at hp
    have hs : s = Finset.univ := Finset.eq_univ_of_card s hp.1
    simpa [minorWeight, hs, permWeight] using permWeight_le_tdet A σ
  · obtain ⟨σ, hσ⟩ := exists_permWeight_eq_tdet A
    have hmem : ((Finset.univ : Finset ι), σ) ∈ admPairs ι (Fintype.card ι) :=
      mem_admPairs.mpr ⟨by simp, by simp⟩
    have hle := le_charCoeff A hmem
    rw [hσ]
    simpa [minorWeight, permWeight] using hle

section Eigen

variable [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}

omit [Fintype ι] [Nonempty ι] in
/-- If `σ` maps the finite set `s` to itself then it permutes `s`, so sums of any
function over `s` are invariant under `σ`. -/
theorem sum_comp_of_mapsTo {s : Finset ι} {σ : Equiv.Perm ι} (hσ : ∀ i ∈ s, σ i ∈ s)
    (g : ι → ℝ) : ∑ i ∈ s, g (σ i) = ∑ i ∈ s, g i := by
  classical
  have himg : s.image σ = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hσ i hi
    · rw [Finset.card_image_of_injective _ σ.injective]
  calc ∑ i ∈ s, g (σ i) = ∑ x ∈ s.image σ, g x :=
        (Finset.sum_image (fun a _ b _ h => σ.injective h)).symm
    _ = ∑ i ∈ s, g i := by rw [himg]

/-- **Upper bound on the characteristic coefficients**: an eigenvalue `lam` forces
`c_k ≤ k · lam`.  (Each cell of the minor loses `lam` plus a telescoping eigenvector
difference, and the differences cancel because `σ` permutes `s`.) -/
theorem charCoeff_le_of_eigen (h : IsTropEigen A lam v) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    charCoeff A k ≤ k * lam := by
  have hne : (admPairs ι k).Nonempty := admPairs_nonempty hk
  rw [charCoeff, dif_pos hne]
  refine Finset.sup'_le _ _ ?_
  rintro ⟨s, σ⟩ hp
  rw [mem_admPairs] at hp
  obtain ⟨hcard, hmaps⟩ := hp
  have hbound : ∑ i ∈ s, A i (σ i) ≤ ∑ i ∈ s, (lam + (v i - v (σ i))) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := h.le_of i (σ i)
    linarith
  have hcancel : ∑ i ∈ s, (lam + (v i - v (σ i))) = k * lam := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_comp_of_mapsTo hmaps v]
    simp [hcard, mul_comm]
  simpa [minorWeight, hcancel] using hbound.trans_eq hcancel

omit [Nonempty ι] in
/-- Extend a self-injective self-map of `s` to a permutation of the whole index set. -/
theorem exists_perm_of_mapsTo {s : Finset ι} {f : ι → ι} (hmaps : ∀ i ∈ s, f i ∈ s)
    (hinj : Set.InjOn f s) : ∃ σ : Equiv.Perm ι, ∀ i ∈ s, σ i = f i := by
  classical
  set g : ι → ι := fun x => if x ∈ s then f x else x with hg
  have hgi : Function.Injective g := by
    intro x y hxy
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · simp only [hg, if_pos hx, if_pos hy] at hxy
      exact hinj hx hy hxy
    · simp only [hg, if_pos hx, if_neg hy] at hxy
      exact absurd (hxy ▸ hmaps x hx) hy
    · simp only [hg, if_neg hx, if_pos hy] at hxy
      exact absurd (hxy ▸ hmaps y hy) hx
    · simpa only [hg, if_neg hx, if_neg hy] using hxy
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hgi), fun i hi => ?_⟩
  simp [Equiv.ofBijective, hg, hi]

/-- **The critical cycle realises a characteristic coefficient**: for some
`1 ≤ k ≤ n` we have `c_k = k · lam`. -/
theorem exists_charCoeff_eq_of_eigen (h : IsTropEigen A lam v) :
    ∃ k : ℕ, 0 < k ∧ k ≤ Fintype.card ι ∧ charCoeff A k = k * lam := by
  classical
  obtain ⟨f, y, p, hp0, hp, hinj, hf, hw⟩ := h.exists_critical_cycle
  set s : Finset ι := (Finset.range p).image (fun t => f^[t] y) with hs
  have hcard : s.card = p := by
    rw [hs, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hperiodic : Function.IsPeriodicPt f p y := hp
  have hmod : ∀ m : ℕ, f^[m % p] y = f^[m] y := hperiodic.iterate_mod_apply
  have hmaps : ∀ i ∈ s, f i ∈ s := by
    intro i hi
    rw [hs, Finset.mem_image] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    rw [Finset.mem_range] at ht
    have hfi : f (f^[t] y) = f^[t + 1] y := (Function.iterate_succ_apply' f t y).symm
    rw [hfi, hs, Finset.mem_image]
    refine ⟨(t + 1) % p, Finset.mem_range.mpr (Nat.mod_lt _ hp0), hmod (t + 1)⟩
  have hinjf : Set.InjOn f s := by
    intro a ha b hb hab
    rw [hs, Finset.coe_image] at ha hb
    obtain ⟨t, ht, rfl⟩ := ha
    obtain ⟨u, hu, rfl⟩ := hb
    simp only [Finset.coe_range, Set.mem_Iio] at ht hu
    have e1 : f (f^[t] y) = f^[(t + 1) % p] y := by
      rw [hmod (t + 1), Function.iterate_succ_apply']
    have e2 : f (f^[u] y) = f^[(u + 1) % p] y := by
      rw [hmod (u + 1), Function.iterate_succ_apply']
    rw [e1, e2] at hab
    have h1 : (t + 1) % p ∈ (Finset.range p : Finset ℕ) :=
      Finset.mem_range.mpr (Nat.mod_lt _ hp0)
    have h2 : (u + 1) % p ∈ (Finset.range p : Finset ℕ) :=
      Finset.mem_range.mpr (Nat.mod_lt _ hp0)
    have hmodeq : (t + 1) % p = (u + 1) % p := hinj (by simpa using h1) (by simpa using h2) hab
    have htu : t = u := by
      have hcase1 : t + 1 < p ∨ t + 1 = p := by omega
      have hcase2 : u + 1 < p ∨ u + 1 = p := by omega
      rcases hcase1 with h1' | h1' <;> rcases hcase2 with h2' | h2'
      · rw [Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2'] at hmodeq; omega
      · rw [Nat.mod_eq_of_lt h1', h2', Nat.mod_self] at hmodeq; omega
      · rw [Nat.mod_eq_of_lt h2', h1', Nat.mod_self] at hmodeq; omega
      · omega
    rw [htu]
  obtain ⟨σ, hσ⟩ := exists_perm_of_mapsTo hmaps hinjf
  have hmem : (s, σ) ∈ admPairs ι p :=
    mem_admPairs.mpr ⟨hcard, fun i hi => by rw [hσ i hi]; exact hmaps i hi⟩
  have hweight : minorWeight A s σ = p * lam := by
    have : minorWeight A s σ = ∑ i ∈ s, A i (f i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hσ i hi]
    rw [this, hs, Finset.sum_image hinj, ← hw, pathWeight]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Function.iterate_succ_apply']
  refine ⟨p, hp0, ?_, le_antisymm ?_ ?_⟩
  · rw [← hcard]; exact Finset.card_le_univ s
  · exact charCoeff_le_of_eigen h (by rw [← hcard]; exact Finset.card_le_univ s)
  · rw [← hweight]; exact le_charCoeff A hmem

end Eigen

-- [dropped: platform already declares charPolyVal]
-- [dropped: platform already declares IsTropicalRoot]
/-- **Tropical eigenvalues are roots of the tropical characteristic polynomial.**
At `x = lam` every degree contributes at most `n·lam`, and the degrees `0` and
`k` (the length of a critical cycle) both attain that value. -/
theorem eigen_isTropicalRoot [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (h : IsTropEigen A lam v) :
    IsTropicalRoot A lam ∧ charPolyVal A lam = (Fintype.card ι : ℝ) * lam := by
  classical
  obtain ⟨k, hk0, hkn, hkeq⟩ := exists_charCoeff_eq_of_eigen h
  have hupper : charPolyVal A lam ≤ (Fintype.card ι : ℝ) * lam := by
    rw [charPolyVal]
    refine Finset.sup'_le _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hj' : j ≤ Fintype.card ι := by omega
    have := charCoeff_le_of_eigen h hj'
    nlinarith [this]
  have hzero : charCoeff A 0 + ((Fintype.card ι : ℝ) - ((0 : ℕ) : ℝ)) * lam
      = (Fintype.card ι : ℝ) * lam := by
    simp
  have hk' : charCoeff A k + ((Fintype.card ι : ℝ) - k) * lam = (Fintype.card ι : ℝ) * lam := by
    rw [hkeq]; ring
  have hmem0 : (0 : ℕ) ∈ Finset.range (Fintype.card ι + 1) := by simp
  have hmemk : k ∈ Finset.range (Fintype.card ι + 1) := Finset.mem_range.mpr (by omega)
  have hlow : (Fintype.card ι : ℝ) * lam ≤ charPolyVal A lam := by
    rw [← hzero, charPolyVal]
    exact Finset.le_sup' (fun j : ℕ => charCoeff A j + ((Fintype.card ι : ℝ) - j) * lam) hmem0
  have hval : charPolyVal A lam = (Fintype.card ι : ℝ) * lam := le_antisymm hupper hlow
  refine ⟨⟨0, k, Nat.zero_le _, hkn, by omega, ?_, ?_⟩, hval⟩
  · rw [hval]; simp
  · rw [hval]; exact hk'

end TropicalLA
section
open TropicalLA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (A : Matrix ι ι ℝ) :
    charCoeff A (Fintype.card ι) = tdet A :=
  TropicalLA.charCoeff_card_eq_tdet A

end
