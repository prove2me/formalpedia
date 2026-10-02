-- Prove2me | solution 1 for BookSixth.bump_perturbation_is_homeomorph_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T07:02:44.974986+00:00
-- url     : https://prove2.me/submissions/696e1249-325d-4090-af8e-9e5666db66fd

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_small_displacement_is_homeomorph
open scoped BigOperators
open BookSixth

-- # A finite bump perturbation of the identity is a homeomorphism
--
-- With `E x = ∑ i, chi i x • (S i x - x)` the target map is `F = id + E`.  The
-- analytic core is the *displacement* bound `‖E x - E y‖ ≤ n * (2 * L + q) * ‖x - y‖`.
--
-- For each index the identity
--
-- ```
-- chi i x • (S i x - x) - chi i y • (S i y - y)
--   = (chi i x - chi i y) • (S i x - x) + chi i y • ((S i x - x) - (S i y - y))
-- ```
--
-- splits the difference into a part controlled by `1`-Lipschitzness of `chi i`
-- together with `‖S i x - x‖ ≤ q`, and a part controlled by `‖chi i y‖ ≤ L`
-- together with `(S i x - x) - (S i y - y) = (S i x - S i y) - (x - y)`, whose
-- norm is at most `2 * ‖x - y‖` because `S i` is `1`-Lipschitz.  Summing over
-- `Fin n` gives the per-index constant `2 * L + q` times the cardinality `n`.
--
-- That displacement bound is exactly the hypothesis of the proved general lemma
-- `BookSixth.small_displacement_is_homeomorph` (target 5f342cbf, ACCEPTED as
-- candidate 3304), applied to `S = F`.  Since `(F x - x) - (F y - y) = E x - E y`
-- the sum terms cancel and the bound transports verbatim.  The lemma supplies the
-- continuous inverse together with both inverse identities; the last conjunct
-- `F x = x + E x` is the definition of `E` read pointwise.
--
-- ASSEMBLY NOTE.  The conclusion is `∃ F, Continuous F ∧ ∃ Finv, Continuous Finv ∧
-- (∀ x, Finv (F x) = x) ∧ (∀ x, F (Finv x) = x) ∧ (∀ x, F x = ...)`.  The two
-- `Exists` levels consume the first four constructor slots, so the fifth slot
-- must be the *entire* remaining term `∀ x, A x ∧ B x ∧ C x`.  That term is an
-- outer `∀` whose body is a right-nested `And`, so it needs one lambda at the
-- top and an angle bracket for each of the two inner `And`s — three bound
-- variables in total.  A flat `⟨…, hleft, hright, …⟩`, a single `And.intro`, and
-- a placeholder inside a nested term were each tried and each fails; the exact
-- diagnostic is "the expected type `∀ x, …` is not an inductive type".

theorem solution (n : ℕ) (L : ℝ) (hL : 0 ≤ L) (q : ℝ) (hq : 0 ≤ q) (hLip : n * (2 * L + q) < 1) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i)) (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i)) (hqL : ∀ i x, ‖S i x - x‖ ≤ q) (hcont : ∀ i, Continuous (S i)) (hchiC : ∀ i, Continuous (chi i)) : ∃ F : Space3 → Space3, Continuous F ∧ ∃ Finv : Space3 → Space3, Continuous Finv ∧ ∀ x, Finv (F x) = x ∧ ∀ x, F (Finv x) = x ∧ ∀ x, F x = x + ∑ i, chi i x • (S i x - x) := by
  classical
  set E : Space3 → Space3 := fun x => ∑ i, chi i x • (S i x - x) with hEdef
  have hEcont : Continuous E := by
    show Continuous (fun x : Space3 => ∑ i, chi i x • (S i x - x))
    fun_prop
  have hchi1 : ∀ (i : Fin n) (a b : Space3), ‖chi i a - chi i b‖ ≤ ‖a - b‖ := by
    intro i a b
    have h := (hchi i).dist_le_mul a b
    rw [NNReal.coe_one, one_mul] at h
    calc ‖chi i a - chi i b‖ = |chi i a - chi i b| := (Real.norm_eq_abs _).symm
      _ = dist (chi i a) (chi i b) := (Real.dist_eq _ _).symm
      _ ≤ dist a b := h
      _ = ‖a - b‖ := (dist_eq_norm a b).symm
  have hS1 : ∀ (i : Fin n) (a b : Space3), ‖S i a - S i b‖ ≤ ‖a - b‖ := by
    intro i a b
    have h := (hS i).dist_le_mul a b
    rw [NNReal.coe_one, one_mul] at h
    calc ‖S i a - S i b‖ = dist (S i a) (S i b) := (dist_eq_norm _ _).symm
      _ ≤ dist a b := h
      _ = ‖a - b‖ := (dist_eq_norm a b).symm
  have hkey : ∀ (i : Fin n) (x y : Space3),
      chi i x • (S i x - x) - chi i y • (S i y - y)
        = (chi i x - chi i y) • (S i x - x)
          + chi i y • ((S i x - x) - (S i y - y)) := by
    intro i x y
    funext j
    simp only [smul_add, add_smul, sub_eq_add_neg, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hEbound : ∀ x y : Space3, ‖E x - E y‖ ≤ n * (2 * L + q) * ‖x - y‖ := by
    intro x y
    have hstep : ∀ i : Fin n,
        ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖
          ≤ (2 * L + q) * ‖x - y‖ := by
      intro i
      have hdiff : ‖(S i x - x) - (S i y - y)‖ ≤ 2 * ‖x - y‖ := by
        rw [show (S i x - x) - (S i y - y) = (S i x - S i y) - (x - y) by abel]
        calc ‖(S i x - S i y) - (x - y)‖ ≤ ‖S i x - S i y‖ + ‖x - y‖ := norm_sub_le _ _
          _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add_left (hS1 i x y) _
          _ = 2 * ‖x - y‖ := by ring
      have htri := norm_add_le ((chi i x - chi i y) • (S i x - x))
        (chi i y • ((S i x - x) - (S i y - y)))
      rw [norm_smul, norm_smul] at htri
      rw [hkey i x y]
      have h1 : ‖(chi i x - chi i y) • (S i x - x)
            + chi i y • ((S i x - x) - (S i y - y))‖
          ≤ ‖chi i x - chi i y‖ * ‖S i x - x‖
            + ‖chi i y‖ * ‖(S i x - x) - (S i y - y)‖ := htri
      have h2 : ‖chi i x - chi i y‖ * ‖S i x - x‖
            + ‖chi i y‖ * ‖(S i x - x) - (S i y - y)‖
          ≤ ‖x - y‖ * q + L * ‖(S i x - x) - (S i y - y)‖ := by
        exact add_le_add
          (mul_le_mul (hchi1 i x y) (hqL i x) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hchiL i y) (norm_nonneg _))
      have h3 : ‖x - y‖ * q + L * ‖(S i x - x) - (S i y - y)‖
          ≤ (2 * L + q) * ‖x - y‖ := by
        have h4 := mul_le_mul_of_nonneg_left hdiff hL
        nlinarith [h4]
      exact h1.trans (h2.trans h3)
    calc ‖E x - E y‖
        ≤ ∑ i, ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖ := by
          simp only [hEdef]
          rw [← Finset.sum_sub_distrib]
          exact norm_sum_le _ _
      _ ≤ ∑ i, (2 * L + q) * ‖x - y‖ := Finset.sum_le_sum fun i _ => hstep i
      _ = (∑ i : Fin n, (2 * L + q)) * ‖x - y‖ := by rw [Finset.sum_mul]
      _ = n * (2 * L + q) * ‖x - y‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hFcont : Continuous (fun x : Space3 => x + E x) := by
    fun_prop
  obtain ⟨Sinv, hSicont, hleft, hright, _⟩ :=
    BookSixth.small_displacement_is_homeomorph (n * (2 * L + q))
      ⟨by positivity, hLip⟩ (fun x : Space3 => x + E x) hFcont (by
        intro x y
        simpa only [hEdef, add_sub_cancel_left] using hEbound x y)
  have hform : ∀ x, x + E x = x + ∑ i, chi i x • (S i x - x) := by
    intro x
    simp only [hEdef]
  refine ⟨fun x : Space3 => x + E x, hFcont, Sinv, hSicont, ?_⟩
  exact fun x => ⟨hleft x, fun y => ⟨hright y, fun z => hform z⟩⟩
