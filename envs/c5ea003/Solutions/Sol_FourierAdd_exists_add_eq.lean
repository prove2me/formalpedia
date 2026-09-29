-- Prove2me | solution 1 for FourierAdd.exists_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:07:39.855692+00:00
-- url     : https://prove2.me/submissions/c030fec2-ed37-4c28-b4fa-386fc35b0b81

-- Sol generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierAdd_card_mul_rep_eq
import Theorems.Thm_FourierAdd_norm_error_lt
/-
# A Fourier-analytic sumset theorem on finite abelian groups

Building on `Catalog.Shared.FourierFiniteAbelian`, this file uses the convolution theorem,
Fourier inversion, Parseval's identity and Cauchy–Schwarz to count representations
`c = a + b` with `a ∈ A`, `b ∈ B` in a finite abelian group `G`.

Main results:

* `FourierAdd.conv_indF` : the convolution of two indicators counts representations.
* `FourierAdd.card_mul_rep_eq` : the Fourier counting formula
  `|G| * r_{A,B}(c) = ∑_ψ ψ(c) · 1̂_A(ψ) · 1̂_B(ψ)`.
* `FourierAdd.norm_error_lt` : the nonprincipal characters contribute strictly less than
  `|A| * |B|` when `(|G| - |A|)(|G| - |B|) < |A||B|`.
* `FourierAdd.exists_add_eq` : consequently `A + B = G`.  The hypothesis turns out to be
  *equivalent* to the pigeonhole bound `|A| + |B| > |G|` (see `cardCondition_iff`), so the
  Fourier/Cauchy–Schwarz route reproduces exactly the pigeonhole threshold — Cauchy–Schwarz is
  tight here.
* `FourierAdd.exists_add_eq_of_card_add_card_gt` : the classical pigeonhole corollary.
* `FourierAdd.cardCondition_iff` : the Cauchy–Schwarz hypothesis is *exactly equivalent* to
  `|A| + |B| > |G|`; so the Fourier route recovers, and does not beat, the pigeonhole threshold.
* `FourierAdd.energy_identity` : the exact Plancherel/additive-energy identity
  `|G| * ∑_c r(c)² = (|A||B|)² + ∑_{ψ ≠ 0} |1̂_A(ψ)|² |1̂_B(ψ)|²`.
* `FourierAdd.card_support_rep_ge` : the resulting quantitative covering bound
  `|{c : r(c) > 0}| ≥ |G| (|A||B|)² / ((|A||B|)² + E)`.
-/


open Finset ComplexConjugate FourierFA

open FourierAdd

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]




/-- The Fourier coefficient of an indicator at the trivial character is the cardinality. -/
@[simp] theorem dft_indF_zero (A : Finset G) : dft (indF A) 0 = (A.card : ℂ) := by
  rw [dft]
  have h : ∀ x : G, conj ((0 : AddChar G ℂ) x) * indF A x
      = if x ∈ A then (1 : ℂ) else 0 := by
    intro x
    simp [indF]
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]




/-- Splitting off the principal character in the counting formula. -/
theorem card_mul_rep_eq_add (A B : Finset G) (c : G) :
    (Fintype.card G : ℂ) * (rep A B c : ℂ)
      = (A.card : ℂ) * (B.card : ℂ)
        + ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
            ψ c * (dft (indF A) ψ * dft (indF B) ψ) := by
  rw [card_mul_rep_eq A B c,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar G ℂ))]
  congr 1
  simp










open FourierAdd in
theorem solution(A B : Finset G)
    (h : ((Fintype.card G : ℝ) - A.card) * ((Fintype.card G : ℝ) - B.card)
      < (A.card : ℝ) * (B.card : ℝ)) (c : G) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  have hkey := card_mul_rep_eq_add A B c
  set S := ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
      ψ c * (dft (indF A) ψ * dft (indF B) ψ) with hS
  have hSreal : S = (((Fintype.card G : ℝ) * (rep A B c : ℝ)
      - (A.card : ℝ) * (B.card : ℝ) : ℝ) : ℂ) := by
    push_cast
    linear_combination -hkey
  have hnorm : ‖S‖ = |(Fintype.card G : ℝ) * (rep A B c : ℝ) - (A.card : ℝ) * (B.card : ℝ)| := by
    rw [hSreal, Complex.norm_real, Real.norm_eq_abs]
  have hlt := norm_error_lt A B c h
  rw [hnorm] at hlt
  have habs := abs_lt.1 hlt
  have hrep : (0 : ℝ) < (Fintype.card G : ℝ) * (rep A B c : ℝ) := by linarith [habs.1]
  have hreppos : 0 < rep A B c := by
    rcases Nat.eq_zero_or_pos (rep A B c) with h0 | h0
    · rw [h0] at hrep
      simp at hrep
    · exact h0
  -- extract a representation
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hreppos
  rw [Finset.mem_filter] at ha
  exact ⟨a, ha.1, c - a, ha.2, by abel⟩
