-- Prove2me | solution 1 for BookSixth.sixthEditionExtension
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-13T01:44:27.273819+00:00
-- url     : https://prove2.me/submissions/90b8ddae-dd25-4638-807c-b261ab64d340

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_spectral
import Theorems.Thm_BookSixth_jacobi_reduction
import Theorems.Thm_BookSixth_hadamard_bound
import Theorems.Thm_BookSixth_hadamard_equality
import Theorems.Thm_BookSixth_hadamard_order
import Theorems.Thm_BookSixth_sylvester
import Theorems.Thm_BookSixth_determinant_lower
import Theorems.Thm_BookSixth_round_circle_unlink
import Theorems.Thm_BookSixth_polynomial_zero_bound
import Theorems.Thm_BookSixth_vanishing_polynomial
import Theorems.Thm_BookSixth_kakeya_bound
import Theorems.Thm_BookSixth_bregman_minc
import Theorems.Thm_BookSixth_latin_bounds
import Theorems.Thm_BookSixth_latin_asymptotic
import Theorems.Thm_BookSixth_hypergraph_two_color
import Theorems.Thm_BookSixth_ramsey_real_bound
import Theorems.Thm_BookSixth_high_girth_chromatic
import Theorems.Thm_BookSixth_crossing_lemma
import Theorems.Thm_BookSixth_determinant_mean_square
import Theorems.Thm_BookSixth_borromean_fox_odd
import Theorems.Thm_BookSixth_tait_fox_five
open scoped BigOperators
open BookSixth

theorem solution :
    (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian),
      ∃ Q : Matrix.unitaryGroup (Fin n) ℝ, ∃ d : Fin n → ℝ,
      star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal d) ∧
    (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (h : 0 < offDiagonalMass A),
      ∃ Q : Matrix.unitaryGroup (Fin n) ℝ,
      offDiagonalMass (star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ)) < offDiagonalMass A) ∧
    (∀ {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A),
      |A.det| ≤ (n : ℝ) ^ ((n : ℝ) / 2)) ∧
    (∀ {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A),
      (|A.det| = (n : ℝ) ^ ((n : ℝ) / 2)) ↔
      ∀ i j, i ≠ j → (∑ k, A k i * A k j) = 0) ∧
    (∀ {n : ℕ} (hn : 2 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) (horth : A.transpose * A = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)),
      4 ∣ n) ∧
    (∀ (m : ℕ),
      ∃ A : Matrix (Fin (2^m)) (Fin (2^m)) ℝ, SignMatrix A ∧
      A.transpose * A = ((2^m : ℕ) : ℝ) • (1 : Matrix (Fin (2^m)) (Fin (2^m)) ℝ)) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, SignMatrix A ∧ Real.sqrt (n.factorial : ℝ) < A.det) ∧
    (∀ {m : ℕ} (C : Fin m → Set Space3) (hround : ∀ i, RoundCircle (C i)) (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)),
      IsUnlink C) ∧
    (∀ {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) F) (hp : p ≠ 0),
      (Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x p = 0)).card ≤
      p.totalDegree * Fintype.card F ^ (n-1)) ∧
    (∀ {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ} (E : Finset (Fin n → F)) (hE : E.card < Nat.choose (n+d) d),
      ∃ p : MvPolynomial (Fin n) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ E, MvPolynomial.eval x p = 0) ∧
    (∀ {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 0 < n) (K : Finset (Fin n → F)) (hK : Kakeya K),
      Nat.choose (Fintype.card F + n - 1) n ≤ K.card ∧
      Fintype.card F ^ n ≤ n.factorial * K.card) ∧
    (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j),
      (permanent A : ℝ) ≤ ∏ i, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^
      (1 / ((∑ j, A i j : ℕ) : ℝ))) ∧
    (∀ (n : ℕ) (hn : 0 < n),
      ((n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) ≤ latinCount n) ∧
      ((latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n,
        (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)))) ∧
    (Filter.Tendsto (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ))
      Filter.atTop (nhds (Real.exp (-2)))) ∧
    (∀ {N d : ℕ} (hd : 2 ≤ d) (A : Finset (Finset (Fin N))) (hsize : ∀ S ∈ A, S.card = d) (hcard : A.card ≤ 2^(d-1)),
      ∃ c : Fin N → Bool, ∀ S ∈ A, ∃ u ∈ S, ∃ v ∈ S, c u ≠ c v) ∧
    (∀ (k N : ℕ) (hk : 2 ≤ k) (hN : (N : ℝ) < (2 : ℝ)^((k : ℝ)/2)),
      ∃ G : SimpleGraph (Fin N), NoMono k G) ∧
    (∀ (k : ℕ) (hk : 2 ≤ k),
      ∃ N : ℕ, ∃ G : SimpleGraph (Fin N), ¬ HasColoring G k ∧
      ∀ l : ℕ, l ≤ k → ¬ HasCycle G l) ∧
    (∀ {N M : ℕ} (hN : 0 < N) (hM : 4*N ≤ M) (D : PlaneDrawing N M),
      M^3 ≤ 64 * N^2 * D.crossings.card) ∧
    (∀ (n : ℕ),
      (∑ B : Fin n → Fin n → Bool, (Matrix.det (fun i j => if B i j then (1 : ℝ) else -1))^2) = (2 : ℝ)^(n*n) * (n.factorial : ℝ)) ∧
    (∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (a b c : ZMod n),
      BorromeanFox a b c ↔ a = b ∧ b = c) ∧
    (∀ (a : Fin 6 → ZMod 5),
      TaitFox a ↔ a 0 = a 2 ∧ a 2 = a 4 ∧ a 1 = a 3 ∧ a 3 = a 5) := by
  exact ⟨@BookSixth.spectral, @BookSixth.jacobi_reduction, @BookSixth.hadamard_bound, @BookSixth.hadamard_equality, @BookSixth.hadamard_order, @BookSixth.sylvester, @BookSixth.determinant_lower, @BookSixth.round_circle_unlink, @BookSixth.polynomial_zero_bound, @BookSixth.vanishing_polynomial, @BookSixth.kakeya_bound, @BookSixth.bregman_minc, @BookSixth.latin_bounds, @BookSixth.latin_asymptotic, @BookSixth.hypergraph_two_color, @BookSixth.ramsey_real_bound, @BookSixth.high_girth_chromatic, @BookSixth.crossing_lemma, @BookSixth.determinant_mean_square, @BookSixth.borromean_fox_odd, @BookSixth.tait_fox_five⟩
