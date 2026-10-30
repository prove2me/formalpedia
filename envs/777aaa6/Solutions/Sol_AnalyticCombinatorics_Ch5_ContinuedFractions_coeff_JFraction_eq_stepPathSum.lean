-- Prove2me | solution 1 for AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_eq_stepPathSum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:29:44.901359+00:00
-- url     : https://prove2.me/submissions/2cd7a4a6-bdb8-45fa-b58a-eaa1c5a8f815

import Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_FlajoletStepPath
import Mathlib

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
# Ch5 §V — Flajolet's theorem on genuine step-list lattice paths

`Flajolet.lean` proves `W h a b c = JFraction h a b c` for the **first-return-coded**
`MotzkinPath` type, where the first-return decomposition is built into the type definition.
This file closes the faithfulness gap: it introduces an **independent** lattice-path object —
a `List Step` together with the floor-0 / ceiling-`h` validity predicate `Walk` and the
return-to-zero / length conditions (`ClosedMotzkin`) — defines its genuine step-product weight
`stepWeight`, and proves a weight-preserving bijection to `MotzkinPath`.  Composing with
`coeff_JFraction_eq_pathSum` upgrades Flajolet's theorem to a statement about real lattice paths
defined as step sequences, with the first-return decomposition now a *theorem*, not a definition.

This file (part 1): the independent definitions and the **structural direction** —
`toSteps` (code → step list), and that it lands in `ClosedMotzkin` with the matching weight.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

lemma endLevel_cons (s : ℕ) (st : Step) (rest : List Step) :
    endLevel s (st :: rest) = endLevel (Step.nextLevel s st) rest := rfl

lemma endLevel_append (s : ℕ) (l₁ l₂ : List Step) :
    endLevel s (l₁ ++ l₂) = endLevel (endLevel s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons st rest ih => simp only [List.cons_append, endLevel_cons, ih]

lemma stepWeight_append (a b c : ℕ → R) (s : ℕ) (l₁ l₂ : List Step) :
    stepWeight a b c s (l₁ ++ l₂)
      = stepWeight a b c s l₁ * stepWeight a b c (endLevel s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [endLevel]
  | cons st rest ih =>
    cases st <;>
      simp only [List.cons_append, stepWeight, endLevel_cons, Step.nextLevel, ih] <;> ring

/-- Running one level higher with the original weights = running at the base with shifted
weights (the arch-interior reindexing).  Needs validity: a down step never leaves the floor,
so the `ℕ`-subtraction in `stepWeight` does not truncate. -/
lemma stepWeight_shift {H : ℕ} (a b c : ℕ → R) {s : ℕ} {p : List Step} (hp : Walk H s p) :
    stepWeight a b c (s + 1) p = stepWeight (shift a) (shift b) (shift c) s p := by
  induction hp with
  | nil => rfl
  | level _ ih => simp only [stepWeight, shift]; rw [ih]
  | up _ _ ih => simp only [stepWeight, shift]; rw [ih]
  | @down s rest _ ih =>
    simp only [stepWeight, Nat.add_sub_cancel, shift]
    rw [ih]

/-- `toSteps` of a code is balanced: it returns to its start level. -/
lemma endLevel_toSteps : ∀ (h n : ℕ) (p : MotzkinPath h n) (s : ℕ),
    endLevel s (toSteps h n p) = s := by
  intro h n p
  induction h, n, p using toSteps.induct <;>
    intro s <;>
    simp_all [toSteps, endLevel_cons, endLevel_append, Step.nextLevel, Nat.add_sub_cancel]

/-- `toSteps` has the right length. -/
lemma toSteps_length : ∀ (h n : ℕ) (p : MotzkinPath h n), (toSteps h n p).length = n := by
  intro h n p
  induction h, n, p using toSteps.induct <;>
    simp_all [toSteps, List.length_append, List.length_cons] <;>
    omega

/-- Level relabel: a valid walk in `[0,h]` from `s` is a valid walk in `[0,h+1]` from `s+1`. -/
lemma Walk_shift {h s : ℕ} {p : List Step} (hp : Walk h s p) : Walk (h + 1) (s + 1) p := by
  induction hp with
  | nil => exact Walk.nil
  | level _ ih => exact Walk.level ih
  | up hle _ ih => exact Walk.up (by omega) ih
  | down _ ih => exact Walk.down ih

/-- Concatenation of valid walks (second starts where the first ends). -/
lemma Walk_append {h : ℕ} : ∀ {s : ℕ} {l₁ l₂ : List Step},
    Walk h s l₁ → Walk h (endLevel s l₁) l₂ → Walk h s (l₁ ++ l₂) := by
  intro s l₁ l₂ h1 h2
  induction h1 with
  | nil => simpa using h2
  | level _ ih =>
      exact Walk.level (ih (by simpa [endLevel_cons, Step.nextLevel] using h2))
  | up hle _ ih =>
      exact Walk.up hle (ih (by simpa [endLevel_cons, Step.nextLevel] using h2))
  | @down s rest _ ih =>
      exact Walk.down (ih (by simpa [endLevel_cons, Step.nextLevel, Nat.add_sub_cancel] using h2))

/-- `toSteps` lands in valid walks from level `0`. -/
lemma toSteps_walk : ∀ (h n : ℕ) (p : MotzkinPath h n), Walk h 0 (toSteps h n p) := by
  intro h n p
  induction h, n, p using toSteps.induct with
  | case1 h a => simp only [toSteps]; exact Walk.nil
  | case2 n a ih => simp only [toSteps]; exact Walk.level ih
  | case3 h a ih => simp only [toSteps]; exact Walk.level Walk.nil
  | case4 h n a rest heq ih => simp only [toSteps, heq]; exact Walk.level ih
  | case5 h n a arch heq ihInner ihRest =>
      simp only [toSteps, heq]
      refine Walk.up (by omega) (Walk_append ?_ ?_)
      · exact Walk_shift ihInner
      · rw [endLevel_toSteps]; exact Walk.down ihRest

/-- **Weight preservation:** the genuine step-product weight of `toSteps h n p` (run from level 0)
equals the first-return-code weight `pathWeight`. -/
lemma stepWeight_toSteps : ∀ (h n : ℕ) (p : MotzkinPath h n) (a b c : ℕ → R),
    stepWeight a b c 0 (toSteps h n p) = pathWeight a b c h n p := by
  intro h n p
  induction h, n, p using toSteps.induct with
  | case1 h pt => intro a b c; simp [toSteps, pathWeight]
  | case2 n pt ih => intro a b c; simp only [toSteps, stepWeight, pathWeight, ih]
  | case3 h pt ih => intro a b c; simp [toSteps, pathWeight, stepWeight]
  | case4 h n sig path heq ih =>
      intro a b c
      simp only [toSteps, heq, pathWeight, stepWeight, ih]
  | case5 h n sig path heq ihInner ihRest =>
      intro a b c
      simp only [toSteps, heq, pathWeight, stepWeight, stepWeight_append,
        endLevel_toSteps, Nat.sub_self]
      rw [stepWeight_shift a b c (toSteps_walk h (↑sig.fst) sig.snd.1),
        ihInner (shift a) (shift b) (shift c), ihRest a b c]
      ring

end
end AnalyticCombinatorics.Ch5.ContinuedFractions

/-!
# Ch5 §V — Flajolet's theorem on genuine step-list lattice paths (the bijection)

This completes the faithfulness upgrade begun in `FlajoletPathBijection.lean`: it proves the
weight-preserving bijection between the first-return-coded `MotzkinPath` type and genuine
lattice paths (`List Step` with the `Walk`/`ClosedMotzkin` validity), and assembles the capstone.

* `Walk_split` — drop a valid prefix (converse of `Walk_append`).
* `toSteps_surjective` — every closed lattice path is `toSteps` of some first-return code
  (the parse, via `first_passage` — the cycle lemma).
* `balanced_split_eq` — first-return uniqueness (two balanced prefixes + `down` agree).
* `toSteps_injective` — distinct codes give distinct step lists.
* `coeff_JFraction_eq_stepPathSum` — **Flajolet's theorem on real lattice paths**: the `z^n`
  coefficient of the bounded J-fraction is the weighted sum over all height-`≤h`, length-`n`
  closed Motzkin step paths, with the first-return decomposition now a *theorem*, not a definition.
-/

open scoped BigOperators PowerSeries

namespace AnalyticCombinatorics.Ch5.ContinuedFractions

noncomputable section

set_option maxHeartbeats 800000

variable {R : Type*} [CommRing R]

/-- Drop a valid prefix: if `l₁ ++ l₂` is a valid walk from `s`, then `l₂` is a valid walk from
`endLevel s l₁`.  (Converse of `Walk_append`.)  Induction on `l₁`. -/
lemma Walk_split {h : ℕ} : ∀ {s : ℕ} {l₁ l₂ : List Step},
    Walk h s (l₁ ++ l₂) → Walk h (endLevel s l₁) l₂ := by
  intro s l₁
  induction l₁ generalizing s with
  | nil => intro l₂ hw; simpa using hw
  | cons st rest ih =>
      intro l₂ hw
      cases st with
      | up =>
          rw [List.cons_append] at hw
          cases hw with
          | up hle sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel] using this
      | down =>
          rw [List.cons_append] at hw
          cases hw with
          | down sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel, Nat.add_sub_cancel] using this
      | level =>
          rw [List.cons_append] at hw
          cases hw with
          | level sub =>
              have := ih sub
              simpa [endLevel_cons, Step.nextLevel] using this

/-- No down step from the floor: a valid walk from level `0` cannot start with `down`. -/
lemma not_walk_zero_down {h : ℕ} {rest : List Step} : ¬ Walk h 0 (Step.down :: rest) := by
  intro hw; cases hw

/-- First-return uniqueness: two balanced valid prefixes each followed by a `down` must agree. -/
lemma balanced_split_eq {h : ℕ} : ∀ {A₁ A₂ B₁ B₂ : List Step},
    Walk h 0 A₁ → endLevel 0 A₁ = 0 → Walk h 0 A₂ → endLevel 0 A₂ = 0 →
    A₁ ++ Step.down :: B₁ = A₂ ++ Step.down :: B₂ → A₁ = A₂ ∧ B₁ = B₂ := by
  intro A₁ A₂ B₁ B₂ hw1 he1 hw2 he2 heq
  rcases List.append_eq_append_iff.mp heq with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · rcases c with _ | ⟨st, c'⟩
    · refine ⟨by simpa using hc1.symm, by simpa using hc2⟩
    · simp only [List.cons_append] at hc2
      obtain ⟨rfl, _⟩ := List.cons.inj hc2
      rw [hc1] at hw2
      have hsp := Walk_split hw2
      rw [he1] at hsp
      exact absurd hsp not_walk_zero_down
  · rcases c with _ | ⟨st, c'⟩
    · refine ⟨by simpa using hc1, by simpa using hc2.symm⟩
    · simp only [List.cons_append] at hc2
      obtain ⟨rfl, _⟩ := List.cons.inj hc2
      rw [hc1] at hw1
      have hsp := Walk_split hw1
      rw [he2] at hsp
      exact absurd hsp not_walk_zero_down

/-- **Injectivity.**  Distinct first-return codes give distinct step lists.  Strong induction on
length: `0`/`1` cases by `Subsingleton`; the `eq_2`/`eq_4` destructure of `q₁,q₂` via the
`simp [toSteps]` constructor equations; the arch case by `balanced_split_eq` + `IH`. -/
lemma toSteps_injective : ∀ (n h : ℕ) (q₁ q₂ : MotzkinPath h n),
    toSteps h n q₁ = toSteps h n q₂ → q₁ = q₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro h q₁ q₂ heq
  rcases n with _ | m
  · have hs : Subsingleton (MotzkinPath h 0) := by rw [MotzkinPath.eq_1]; infer_instance
    exact Subsingleton.elim q₁ q₂
  · rcases h with _ | h'
    · -- h = 0, n = m+1
      have h1 : q₁ = (MotzkinPath.eq_2 m).mpr ((MotzkinPath.eq_2 m).mp q₁) := by simp
      have h2 : q₂ = (MotzkinPath.eq_2 m).mpr ((MotzkinPath.eq_2 m).mp q₂) := by simp
      have hmp : (MotzkinPath.eq_2 m).mp q₁ = (MotzkinPath.eq_2 m).mp q₂ := by
        apply IH m (by omega) 0
        have hd1 : toSteps 0 (m + 1) q₁
            = Step.level :: toSteps 0 m ((MotzkinPath.eq_2 m).mp q₁) := by
          conv_lhs => rw [h1]
          simp [toSteps]
        have hd2 : toSteps 0 (m + 1) q₂
            = Step.level :: toSteps 0 m ((MotzkinPath.eq_2 m).mp q₂) := by
          conv_lhs => rw [h2]
          simp [toSteps]
        rw [hd1, hd2] at heq
        simpa using heq
      rw [h1, h2, hmp]
    · rcases m with _ | k
      · have hs : Subsingleton (MotzkinPath (h' + 1) 1) := by
          rw [MotzkinPath.eq_3, MotzkinPath.eq_1]; infer_instance
        exact Subsingleton.elim q₁ q₂
      · -- h'+1, n = k+2
        have h1 : q₁ = (MotzkinPath.eq_4 h' k).mpr ((MotzkinPath.eq_4 h' k).mp q₁) := by simp
        have h2 : q₂ = (MotzkinPath.eq_4 h' k).mpr ((MotzkinPath.eq_4 h' k).mp q₂) := by simp
        have hmp : (MotzkinPath.eq_4 h' k).mp q₁ = (MotzkinPath.eq_4 h' k).mp q₂ := by
          rcases hsv1 : (MotzkinPath.eq_4 h' k).mp q₁ with r₁ | a₁ <;>
            rcases hsv2 : (MotzkinPath.eq_4 h' k).mp q₂ with r₂ | a₂
          · -- inl, inl
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.level :: toSteps (h' + 1) (k + 1) r₁ := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.level :: toSteps (h' + 1) (k + 1) r₂ := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq
            rw [IH (k + 1) (by omega) (h' + 1) r₁ r₂ (by simpa using heq)]
          · -- inl, inr : impossible
            exfalso
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.level :: toSteps (h' + 1) (k + 1) r₁ := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.up :: (toSteps h' a₂.1.1 a₂.2.1
                  ++ Step.down :: toSteps (h' + 1) (k - a₂.1.1) a₂.2.2) := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq; simp at heq
          · -- inr, inl : impossible
            exfalso
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.up :: (toSteps h' a₁.1.1 a₁.2.1
                  ++ Step.down :: toSteps (h' + 1) (k - a₁.1.1) a₁.2.2) := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.level :: toSteps (h' + 1) (k + 1) r₂ := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq; simp at heq
          · -- inr, inr : arch
            obtain ⟨i₁, inner₁, rest₁⟩ := a₁
            obtain ⟨i₂, inner₂, rest₂⟩ := a₂
            have hd1 : toSteps (h' + 1) (k + 2) q₁
                = Step.up :: (toSteps h' i₁.1 inner₁
                  ++ Step.down :: toSteps (h' + 1) (k - i₁.1) rest₁) := by
              conv_lhs => rw [h1, hsv1]
              simp [toSteps]
            have hd2 : toSteps (h' + 1) (k + 2) q₂
                = Step.up :: (toSteps h' i₂.1 inner₂
                  ++ Step.down :: toSteps (h' + 1) (k - i₂.1) rest₂) := by
              conv_lhs => rw [h2, hsv2]
              simp [toSteps]
            rw [hd1, hd2] at heq
            have heq' : toSteps h' i₁.1 inner₁ ++ Step.down :: toSteps (h' + 1) (k - i₁.1) rest₁
                = toSteps h' i₂.1 inner₂ ++ Step.down :: toSteps (h' + 1) (k - i₂.1) rest₂ := by
              simpa using heq
            obtain ⟨hMeq, hBeq⟩ := balanced_split_eq (toSteps_walk h' i₁.1 inner₁)
              (endLevel_toSteps h' i₁.1 inner₁ 0) (toSteps_walk h' i₂.1 inner₂)
              (endLevel_toSteps h' i₂.1 inner₂ 0) heq'
            have hi : i₁.1 = i₂.1 := by
              have hl := congrArg List.length hMeq
              rwa [toSteps_length, toSteps_length] at hl
            have hii : i₁ = i₂ := Fin.ext hi
            subst hii
            have hin : inner₁ = inner₂ := IH i₁.1 (by omega) h' inner₁ inner₂ hMeq
            have hre : rest₁ = rest₂ := IH (k - i₁.1) (by omega) (h' + 1) rest₁ rest₂ hBeq
            rw [hin, hre]
        rw [h1, h2, hmp]

end
end AnalyticCombinatorics.Ch5.ContinuedFractions

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.ContinuedFractions
open scoped BigOperators PowerSeries
set_option maxHeartbeats 800000
variable {R : Type*} [CommRing R]
theorem solution (h n : ℕ) (a b c : ℕ → R) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = ∑ p ∈ closedMotzkinFinset h n, stepWeight a b c 0 p := by
  rw [PathSum.coeff_JFraction_eq_pathSum, WpathSum]
  rw [closedMotzkinFinset,
    Finset.sum_image (fun q₁ _ q₂ _ hq => toSteps_injective n h q₁ q₂ hq)]
  exact Finset.sum_congr rfl (fun q _ => (stepWeight_toSteps h n q a b c).symm)
