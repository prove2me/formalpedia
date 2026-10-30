-- Prove2me | solution 1 for AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_height_indep
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:45:52.160784+00:00
-- url     : https://prove2.me/submissions/243132ed-40cf-4327-884b-17d597eafbe2

import Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_Flajolet
import Mathlib

namespace AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum end AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Flajolet's bounded continued fraction for weighted Motzkin paths

This file formalizes the finite, bounded-height version of Flajolet's
continued-fraction theorem.  Paths are finite first-return-coded Motzkin paths
with a projection to step lists.  A down step from level `k + 1` to level `k`
has weight `b k`; equivalently, when the current level is `m`, a down step has
weight `b (m - 1)`.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

/- The recursive finite path type and the power-series induction below create
moderately large goals after unfolding `Finset.univ` over sum/sigma types. -/
set_option maxHeartbeats 800000

@[simp] theorem coeff_W {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) (n : ℕ) :
    PowerSeries.coeff (R := R) n (W h a b c) = Wcoeff h a b c n := by
  simp [W]

@[simp] theorem Wcoeff_zero_length {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    Wcoeff h a b c 0 = 1 := by
  simp [Wcoeff]

theorem Wcoeff_height_zero_succ {R : Type*} [CommRing R]
    (a b c : ℕ → R) (n : ℕ) :
    Wcoeff 0 a b c (n + 1) = c 0 * Wcoeff 0 a b c n := by
  simp [Wcoeff]

theorem Wcoeff_succ_one {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    Wcoeff (h + 1) a b c 1 = c 0 := by
  simp [Wcoeff]

theorem Wcoeff_succ_succ {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    Wcoeff (h + 1) a b c (n + 2) =
      c 0 * Wcoeff (h + 1) a b c (n + 1) +
        a 0 * b 0 *
          ∑ i : Fin (n + 1),
            Wcoeff h (shift a) (shift b) (shift c) i.1 *
              Wcoeff (h + 1) a b c (n - i.1) := by
  simp [Wcoeff]

/-- Height zero: only level steps are possible. -/
theorem W_height_zero_eq_inv {R : Type*} [CommRing R] (a b c : ℕ → R) :
    W 0 a b c =
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := by
  set_option backward.isDefEq.respectTransparency false in
    have hmul : geomDenom (c 0) * W 0 a b c = 1 := by
      have hseries :
          W 0 a b c = 1 + PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c := by
        ext n
        cases n with
        | zero =>
            simp
        | succ n =>
            simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
              zero_add, coeff_W]
            rw [Wcoeff_height_zero_succ]
            rw [show PowerSeries.coeff (R := R) (n + 1)
                (PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c) =
                  c 0 * Wcoeff 0 a b c n by
              rw [mul_assoc]
              simp]
      calc
        geomDenom (c 0) * W 0 a b c =
            W 0 a b c - PowerSeries.C (c 0) * PowerSeries.X * W 0 a b c := by
          simp [geomDenom]
          ring
        _ = 1 := by
          nth_rewrite 1 [hseries]
          abel
    have hleft :
        PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) * geomDenom (c 0) = 1 := by
      exact PowerSeries.invOfUnit_mul (geomDenom (c 0)) (1 : Rˣ)
        (by simp [geomDenom])
    calc
      W 0 a b c = 1 * W 0 a b c := by simp
      _ = (PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) * geomDenom (c 0)) *
          W 0 a b c := by rw [hleft]
      _ = PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) *
          (geomDenom (c 0) * W 0 a b c) := by ring
      _ = PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := by rw [hmul, mul_one]

@[simp] theorem constantCoeff_cfDenom {R : Type*} [CommRing R]
    (a b c : ℕ → R) (tail : PowerSeries R) :
    PowerSeries.constantCoeff (cfDenom a b c tail) = 1 := by
  simp [cfDenom]

theorem coeff_quadratic_term {R : Type*} [CommRing R]
    (A : R) (P Q : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (R := R) (n + 2)
        (PowerSeries.C A * PowerSeries.X ^ 2 * (P * Q)) =
      A * ∑ i : Fin (n + 1),
        PowerSeries.coeff (R := R) i.1 P *
          PowerSeries.coeff (R := R) (n - i.1) Q := by
  set_option backward.isDefEq.respectTransparency false in
    rw [mul_assoc]
    simp only [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_X_pow_mul (p := P * Q) (n := 2) (d := n)]
    rw [PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => PowerSeries.coeff (R := R) x P *
        PowerSeries.coeff (R := R) y Q) n]
    rw [Finset.sum_fin_eq_sum_range]
    apply congrArg (fun z => A * z)
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp [hi']

theorem W_first_return_series {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    W (h + 1) a b c =
      1 + PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c +
        PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
          (W h (shift a) (shift b) (shift c) * W (h + 1) a b c) := by
  set_option backward.isDefEq.respectTransparency false in
    ext n
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            simp only [map_add, PowerSeries.coeff_one, coeff_W]
            rw [Wcoeff_succ_one]
            rw [show PowerSeries.coeff (R := R) 1
                (PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c) = c 0 by
              rw [mul_assoc]
              simp]
            rw [show PowerSeries.coeff (R := R) 1
                (PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
                  (W h (shift a) (shift b) (shift c) * W (h + 1) a b c)) = 0 by
              simp only [mul_assoc, PowerSeries.coeff_C_mul]
              rw [PowerSeries.coeff_X_pow_mul'
                (p := W h (shift a) (shift b) (shift c) * W (h + 1) a b c)
                (n := 2) (d := 1)]
              simp]
            simp
        | succ m =>
            simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
              zero_add, coeff_W]
            rw [show m + 1 + 1 = m + 2 by omega]
            rw [Wcoeff_succ_succ]
            rw [show PowerSeries.coeff (R := R) (m + 2)
                (PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c) =
                  c 0 * Wcoeff (h + 1) a b c (m + 1) by
              rw [mul_assoc]
              simp]
            rw [coeff_quadratic_term]
            simp [coeff_W]

theorem W_mul_cfDenom_self {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    cfDenom a b c (W h (shift a) (shift b) (shift c)) * W (h + 1) a b c = 1 := by
  set_option backward.isDefEq.respectTransparency false in
    have hfr := W_first_return_series h a b c
    calc
      cfDenom a b c (W h (shift a) (shift b) (shift c)) * W (h + 1) a b c =
          W (h + 1) a b c -
            PowerSeries.C (c 0) * PowerSeries.X * W (h + 1) a b c -
            PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 *
              (W h (shift a) (shift b) (shift c) * W (h + 1) a b c) := by
        simp [cfDenom]
        ring
      _ = 1 := by
        nth_rewrite 1 [hfr]
        abel

/-- Flajolet's finite continued-fraction theorem, bounded height. -/
theorem flajolet_cf {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    W h a b c = JFraction h a b c := by
  set_option backward.isDefEq.respectTransparency false in
    induction h generalizing a b c with
    | zero =>
        exact W_height_zero_eq_inv a b c
    | succ h ih =>
        have htail :
            W h (shift a) (shift b) (shift c) =
              JFraction h (shift a) (shift b) (shift c) := ih _ _ _
        have hmul :
            cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) *
                W (h + 1) a b c = 1 := by
          simpa [htail] using W_mul_cfDenom_self h a b c
        have hleft :
            PowerSeries.invOfUnit
                (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
              cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) = 1 := by
          exact PowerSeries.invOfUnit_mul
            (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ)
            (by simp)
        calc
          W (h + 1) a b c = 1 * W (h + 1) a b c := by simp
          _ =
              (PowerSeries.invOfUnit
                  (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
                cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) *
                  W (h + 1) a b c := by rw [hleft]
          _ =
              PowerSeries.invOfUnit
                  (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) *
                (cfDenom a b c (JFraction h (shift a) (shift b) (shift c)) *
                  W (h + 1) a b c) := by ring
          _ =
              PowerSeries.invOfUnit
                  (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) := by
            rw [hmul, mul_one]
          _ = JFraction (h + 1) a b c := rfl

end
end AnalyticCombinatorics.Ch5.ContinuedFractions

/-!
# Path-sum coefficients for Flajolet's bounded continued fraction

This file bridges the literal finite path sum from `MotzkinPath` to the
first-return recursive coefficients used by `W`.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

noncomputable section

/- Splitting `Fintype.univ` over the recursive `Sum`/`Sigma` path code creates
large finite-sum goals after unfolding `pathWeight`. -/
set_option maxHeartbeats 800000

open AnalyticCombinatorics.Ch5.ContinuedFractions

/-- Summing over a recursive type is unchanged by the `Eq.mp` to its unfolded code. -/
private theorem fintype_sum_eq_mp {α β : Type u} {M : Type v}
    [Fintype α] [Fintype β] [AddCommMonoid M]
    (h : α = β) (f : β → M) :
    (∑ x : α, f (h.mp x)) = ∑ x : β, f x := by
  simpa [Equiv.cast, cast] using Equiv.sum_comp (Equiv.cast h) f

/-- The literal path sum satisfies the same first-return recursion as `Wcoeff`. -/
theorem WpathSum_eq_Wcoeff {R : Type*} [CommRing R] (h n : ℕ) (a b c : ℕ → R) :
    WpathSum h a b c n = Wcoeff h a b c n := by
  induction h, a, b, c, n using Wcoeff.induct with
  | case1 h a b c =>
      simp [WpathSum, pathWeight, MotzkinPath]
  | case2 a b c n ih =>
      rw [WpathSum, Wcoeff]
      simp only [pathWeight]
      change
        (∑ x : MotzkinPath 0 (n + 1),
          c 0 * pathWeight a b c 0 n ((MotzkinPath.eq_2 n).mp x)) =
          c 0 * Wcoeff 0 a b c n
      rw [fintype_sum_eq_mp (MotzkinPath.eq_2 n)
        (fun x : MotzkinPath 0 n => c 0 * pathWeight a b c 0 n x)]
      rw [← Finset.mul_sum]
      exact congrArg (fun x => c 0 * x) ih
  | case3 h a b c =>
      simp [WpathSum, Wcoeff, pathWeight, MotzkinPath]
  | case4 h a b c n ihLevel ihInner ihRest =>
      rw [WpathSum, Wcoeff]
      simp only [pathWeight]
      change
        (∑ x : MotzkinPath h.succ n.succ.succ,
          (fun y :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
            match y with
            | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
            | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
            ((MotzkinPath.eq_4 h n).mp x)) =
          c 0 * Wcoeff (h + 1) a b c (n + 1) +
            a 0 * b 0 *
              ∑ i : Fin (n + 1),
                Wcoeff h (shift a) (shift b) (shift c) i.1 *
                  Wcoeff (h + 1) a b c (n - i.1)
      calc
        (∑ x : MotzkinPath h.succ n.succ.succ,
          (fun y :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
            match y with
            | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
            | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
            ((MotzkinPath.eq_4 h n).mp x))
            =
            ∑ x :
              MotzkinPath (h + 1) (n + 1) ⊕
                (Σ i : Fin (n + 1),
                  MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)),
              match x with
              | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
              | Sum.inr arch =>
                  a 0 * b 0 *
                    pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                      pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2 := by
          exact fintype_sum_eq_mp (MotzkinPath.eq_4 h n)
            (fun x :
                MotzkinPath (h + 1) (n + 1) ⊕
                  (Σ i : Fin (n + 1),
                    MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)) =>
              match x with
              | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
              | Sum.inr arch =>
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2)
        _ =
            (∑ rest : MotzkinPath (h + 1) (n + 1),
              c 0 * pathWeight a b c (h + 1) (n + 1) rest) +
              ∑ arch :
                  (Σ i : Fin (n + 1),
                    MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)),
                a 0 * b 0 *
                  pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
                    pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2 := by
          rw [Fintype.sum_sum_type]
        _ =
            c 0 * WpathSum (h + 1) a b c (n + 1) +
              a 0 * b 0 *
                ∑ i : Fin (n + 1),
                  WpathSum h (shift a) (shift b) (shift c) i.1 *
                  WpathSum (h + 1) a b c (n - i.1) := by
          congr 1
          · rw [← Finset.mul_sum]
            rfl
          · rw [Fintype.sum_sigma]
            simp_rw [Fintype.sum_prod_type]
            simp_rw [mul_assoc]
            simp_rw [← Finset.mul_sum]
            apply congrArg (fun x => a 0 * (b 0 * x))
            apply Finset.sum_congr rfl
            intro i _hi
            rw [← Finset.sum_mul]
            rfl
        _ =
            c 0 * Wcoeff (h + 1) a b c (n + 1) +
              a 0 * b 0 *
                ∑ i : Fin (n + 1),
                  Wcoeff h (shift a) (shift b) (shift c) i.1 *
                    Wcoeff (h + 1) a b c (n - i.1) := by
          rw [ihLevel]
          apply congrArg (fun x =>
            c 0 * Wcoeff (h + 1) a b c (n + 1) + a 0 * b 0 * x)
          apply Finset.sum_congr rfl
          intro i _hi
          rw [ihInner i, ihRest i]

/-- Coefficients of the bounded J-fraction are the literal finite path sums. -/
theorem coeff_JFraction_eq_pathSum {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c) = WpathSum h a b c n := by
  rw [← flajolet_cf h a b c, coeff_W, WpathSum_eq_Wcoeff]

end
end AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

/-!
# Ch5 §V — Flajolet's continued fraction theorem: removing the height bound

`Flajolet.lean` / `FlajoletPathSum.lean` prove the **bounded-height** form
`flajolet_cf` / `coeff_JFraction_eq_pathSum`: for every height bound `h`, the
height-`h` J-fraction's coefficients are the height-`h` Motzkin path sums.

The bound is immaterial for the coefficient of `z^n`: a Motzkin path of length
`n` (which returns to level 0) can never reach relative height above `n`, so the
length-`n` coefficient stabilizes once `h ≥ n`. This file proves that
stabilization, lifting the theorem off the height restriction:

* `Wcoeff_height_indep` — `Wcoeff h a b c n = Wcoeff k a b c n` whenever
  `n ≤ h` and `n ≤ k` (the coefficient is independent of the height bound
  above the length).
* `coeff_JFraction_height_indep` — the height-`h` J-fraction's `z^n` coefficient
  equals the height-`n` one for any `h ≥ n`; i.e. the bounded J-fraction agrees
  with the full (unbounded) continued fraction in every coefficient.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

/-- The height-`h` coefficient of length `n` does not depend on the height bound,
provided the bound is at least the length (a length-`n` path never exceeds
relative height `n`). Strong induction on the length. -/
theorem Wcoeff_height_indep {R : Type*} [CommRing R] :
    ∀ (n h k : ℕ) (a b c : ℕ → R), n ≤ h → n ≤ k →
      Wcoeff h a b c n = Wcoeff k a b c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h k a b c hh hk
    rcases n with _ | _ | m
    · -- n = 0
      simp
    · -- n = 1
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Wcoeff_succ_one, Wcoeff_succ_one]
    · -- n = m + 2
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have e1 : Wcoeff (h' + 1) a b c (m + 1) = Wcoeff (k' + 1) a b c (m + 1) :=
        ih (m + 1) (by omega) (h' + 1) (k' + 1) a b c (by omega) (by omega)
      have e2 : ∀ i : Fin (m + 1),
          Wcoeff h' (shift a) (shift b) (shift c) i.1
            = Wcoeff k' (shift a) (shift b) (shift c) i.1 := fun i =>
        ih i.1 (by have := i.2; omega) h' k' (shift a) (shift b) (shift c)
          (by have := i.2; omega) (by have := i.2; omega)
      have e3 : ∀ i : Fin (m + 1),
          Wcoeff (h' + 1) a b c (m - i.1) = Wcoeff (k' + 1) a b c (m - i.1) := fun i =>
        ih (m - i.1) (by have := i.2; omega) (h' + 1) (k' + 1) a b c
          (by omega) (by omega)
      have hsum :
          (∑ i : Fin (m + 1),
              Wcoeff h' (shift a) (shift b) (shift c) i.1
                * Wcoeff (h' + 1) a b c (m - i.1))
            = (∑ i : Fin (m + 1),
              Wcoeff k' (shift a) (shift b) (shift c) i.1
                * Wcoeff (k' + 1) a b c (m - i.1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [e2 i, e3 i])
      rw [Wcoeff_succ_succ, Wcoeff_succ_succ, e1, hsum]

/-- The height-`h` coefficient of length `n` equals the height-`n` value
(for `h ≥ n`): the canonical height-bounded representative of the unbounded
coefficient. -/
theorem Wcoeff_eq_at_length {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) (hn : n ≤ h) :
    Wcoeff h a b c n = Wcoeff n a b c n :=
  Wcoeff_height_indep n h n a b c hn le_rfl

end AnalyticCombinatorics.Ch5.ContinuedFractions

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.ContinuedFractions
open scoped BigOperators PowerSeries
open AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum in
theorem solution {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) (hn : n ≤ h) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = PowerSeries.coeff (R := R) n (JFraction n a b c) := by
  rw [coeff_JFraction_eq_pathSum, coeff_JFraction_eq_pathSum,
    WpathSum_eq_Wcoeff, WpathSum_eq_Wcoeff, Wcoeff_eq_at_length h n a b c hn]
