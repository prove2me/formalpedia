-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_Flajolet
-- name    : AnalyticCombinatorics_Ch5_ContinuedFractions_Flajolet
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:23:46.673997+00:00
-- url     : https://prove2.me/theorems/3d0f21b3-810c-46bb-a5db-2a4939415f7c
-- title:
--   Finite J-fractions and coded weighted Motzkin paths
-- statement:
--   For natural height h and length n, first-return-coded Motzkin paths are finite recursive types. Step weights at level k are a(k) upward, b(k) downward from k+1, and c(k) level. WpathSum is their total weight; Wcoeff gives the recursive coefficient family and W its formal series. The finite J-fraction has base 1/(1-c(0)X) and recursive denominator 1-c(0)X-a(0)b(0)X² times the shifted tail, over an arbitrary commutative ring.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/ContinuedFractions/Flajolet.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

/-- Motzkin steps. -/
inductive Step where
  | up
  | down
  | level
  deriving DecidableEq, Repr

namespace Step

/-- The endpoint after taking one step from a natural-number level.
Invalid down steps from level `0` are sent to `0`; the path type below never
uses such a step at the bottom level. -/
def nextLevel : ℕ → Step → ℕ
  | k, up => k + 1
  | k, down => k - 1
  | k, level => k

end Step

/-- Shift a coefficient family upward by one level. -/
def shift (f : ℕ → R) : ℕ → R :=
  fun k => f (k + 1)

/-- A first-return-coded Motzkin path of length `n`, from level `0` back to
level `0`, staying at relative height at most `h`.

For positive height and length at least two, a path is either a bottom level
step followed by a path, or an arch
`up :: inner ++ down :: rest`; the inner path has height bound one smaller and
uses shifted weights in the generating function. -/
def MotzkinPath : ℕ → ℕ → Type
  | _h, 0 => PUnit
  | 0, n + 1 => MotzkinPath 0 n
  | h + 1, 1 => MotzkinPath (h + 1) 0
  | h + 1, n + 2 =>
      MotzkinPath (h + 1) (n + 1) ⊕
        (Σ i : Fin (n + 1),
          MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1))
termination_by h n => h + n
decreasing_by
  all_goals omega

set_option linter.unusedVariables false in
/-- Decidable equality for the recursive finite path code. -/
def motzkinPathDecidableEq : (h n : ℕ) → DecidableEq (MotzkinPath h n)
  | h, 0 => by
      unfold MotzkinPath
      infer_instance
  | 0, n + 1 => by
      unfold MotzkinPath
      exact motzkinPathDecidableEq 0 n
  | h + 1, 1 => by
      unfold MotzkinPath
      exact motzkinPathDecidableEq (h + 1) 0
  | h + 1, n + 2 => by
      unfold MotzkinPath
      letI := motzkinPathDecidableEq (h + 1) (n + 1)
      letI inner : (i : Fin (n + 1)) → DecidableEq (MotzkinPath h i.1) :=
        fun i => motzkinPathDecidableEq h i.1
      letI rest : (i : Fin (n + 1)) →
          DecidableEq (MotzkinPath (h + 1) (n - i.1)) :=
        fun i => motzkinPathDecidableEq (h + 1) (n - i.1)
      infer_instance
termination_by h n => h + n
decreasing_by
  all_goals omega

set_option linter.unusedVariables false in
/-- Finiteness for the recursive finite path code. -/
def motzkinPathFintype : (h n : ℕ) → Fintype (MotzkinPath h n)
  | h, 0 => by
      unfold MotzkinPath
      infer_instance
  | 0, n + 1 => by
      unfold MotzkinPath
      exact motzkinPathFintype 0 n
  | h + 1, 1 => by
      unfold MotzkinPath
      exact motzkinPathFintype (h + 1) 0
  | h + 1, n + 2 => by
      unfold MotzkinPath
      letI := motzkinPathFintype (h + 1) (n + 1)
      letI inner : (i : Fin (n + 1)) → Fintype (MotzkinPath h i.1) :=
        fun i => motzkinPathFintype h i.1
      letI rest : (i : Fin (n + 1)) →
          Fintype (MotzkinPath (h + 1) (n - i.1)) :=
        fun i => motzkinPathFintype (h + 1) (n - i.1)
      infer_instance
termination_by h n => h + n
decreasing_by
  all_goals omega

instance (h n : ℕ) : DecidableEq (MotzkinPath h n) :=
  motzkinPathDecidableEq h n

instance (h n : ℕ) : Fintype (MotzkinPath h n) :=
  motzkinPathFintype h n

/-- Weight of a coded path.  In an arch, the initial up and final down
contribute `a 0` and `b 0`; the inside is evaluated with all weights shifted
up one absolute level. -/
def pathWeight {R : Type*} [CommRing R]
    (a b c : ℕ → R) : (h n : ℕ) → MotzkinPath h n → R
  | _h, 0, _p => 1
  | 0, n + 1, p =>
      c 0 * pathWeight a b c 0 n (by simpa [MotzkinPath] using p)
  | h + 1, 1, p =>
      c 0 * pathWeight a b c (h + 1) 0 (by simpa [MotzkinPath] using p)
  | h + 1, n + 2, p =>
      match
        (by
          simpa [MotzkinPath] using p :
            MotzkinPath (h + 1) (n + 1) ⊕
              (Σ i : Fin (n + 1),
                MotzkinPath h i.1 × MotzkinPath (h + 1) (n - i.1)))
      with
      | Sum.inl rest => c 0 * pathWeight a b c (h + 1) (n + 1) rest
      | Sum.inr arch =>
          a 0 * b 0 *
            pathWeight (shift a) (shift b) (shift c) h arch.1.1 arch.2.1 *
              pathWeight a b c (h + 1) (n - arch.1.1) arch.2.2
termination_by h n _p => h + n
decreasing_by
  all_goals omega

/-- The literal finite sum over coded paths.  The main coefficient function below
uses the first-return recursion induced by this finite code. -/
def WpathSum {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) (n : ℕ) : R :=
  ∑ p : MotzkinPath h n, pathWeight a b c h n p

/-- The coefficient of the bounded-height weighted Motzkin generating function,
computed by the first-return decomposition of `MotzkinPath`. -/
def Wcoeff {R : Type*} [CommRing R] :
    ℕ → (ℕ → R) → (ℕ → R) → (ℕ → R) → ℕ → R
  | _h, _a, _b, _c, 0 => 1
  | 0, _a, _b, c, n + 1 => c 0 * Wcoeff 0 _a _b c n
  | _h + 1, _a, _b, c, 1 => c 0
  | h + 1, a, b, c, n + 2 =>
      c 0 * Wcoeff (h + 1) a b c (n + 1) +
        a 0 * b 0 *
          ∑ i : Fin (n + 1),
            Wcoeff h (shift a) (shift b) (shift c) i.1 *
              Wcoeff (h + 1) a b c (n - i.1)
termination_by h _a _b _c n => h + n
decreasing_by
  all_goals omega

/-- The bounded-height weighted Motzkin ordinary generating function. -/
def W {R : Type*} [CommRing R] (h : ℕ) (a b c : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => Wcoeff h a b c n

def geomDenom {R : Type*} [CommRing R] (u : R) : PowerSeries R :=
  1 - PowerSeries.C u * PowerSeries.X

def cfDenom {R : Type*} [CommRing R]
    (a b c : ℕ → R) (tail : PowerSeries R) : PowerSeries R :=
  1 - PowerSeries.C (c 0) * PowerSeries.X -
    PowerSeries.C (a 0 * b 0) * PowerSeries.X ^ 2 * tail

/-- The finite J-fraction tail, measured from the current bottom level. -/
def JFraction {R : Type*} [CommRing R] :
    ℕ → (ℕ → R) → (ℕ → R) → (ℕ → R) → PowerSeries R
  | 0, _a, _b, c =>
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ)
  | h + 1, a, b, c =>
      PowerSeries.invOfUnit
        (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ)

@[simp] theorem JFraction_zero {R : Type*} [CommRing R] (a b c : ℕ → R) :
    JFraction 0 a b c =
      PowerSeries.invOfUnit (geomDenom (c 0)) (1 : Rˣ) := rfl

@[simp] theorem JFraction_succ {R : Type*} [CommRing R]
    (h : ℕ) (a b c : ℕ → R) :
    JFraction (h + 1) a b c =
      PowerSeries.invOfUnit
        (cfDenom a b c (JFraction h (shift a) (shift b) (shift c))) (1 : Rˣ) := rfl

end

end AnalyticCombinatorics.Ch5.ContinuedFractions


