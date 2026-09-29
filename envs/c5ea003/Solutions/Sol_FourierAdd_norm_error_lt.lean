-- Prove2me | solution 1 for FourierAdd.norm_error_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:06:02.273441+00:00
-- url     : https://prove2.me/submissions/c7b14927-bbac-41a7-bc4b-511202c16d39

-- Sol generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierAdd_norm_error_le
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


















open FourierAdd in
theorem solution(A B : Finset G) (c : G)
    (h : ((Fintype.card G : ℝ) - A.card) * ((Fintype.card G : ℝ) - B.card)
      < (A.card : ℝ) * (B.card : ℝ)) :
    ‖∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
        ψ c * (dft (indF A) ψ * dft (indF B) ψ)‖ < (A.card : ℝ) * (B.card : ℝ) := by
  have hAle : (A.card : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast Finset.card_le_univ A
  have hBle : (B.card : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast Finset.card_le_univ B
  have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  -- both sets must be nonempty
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    rcases lt_or_eq_of_le hA0 with h' | h'
    · exact h'
    · exfalso
      rw [← h'] at h
      nlinarith [sub_nonneg.2 hBle]
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by
    rcases lt_or_eq_of_le hB0 with h' | h'
    · exact h'
    · exfalso
      rw [← h'] at h
      nlinarith [sub_nonneg.2 hAle]
  have hcs := norm_error_le A B c
  have hprod : ((Fintype.card G : ℝ) * A.card - (A.card : ℝ) ^ 2)
      * ((Fintype.card G : ℝ) * B.card - (B.card : ℝ) ^ 2)
      < ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by
    have e1 : (Fintype.card G : ℝ) * A.card - (A.card : ℝ) ^ 2
        = (A.card : ℝ) * ((Fintype.card G : ℝ) - A.card) := by ring
    have e2 : (Fintype.card G : ℝ) * B.card - (B.card : ℝ) ^ 2
        = (B.card : ℝ) * ((Fintype.card G : ℝ) - B.card) := by ring
    rw [e1, e2]
    have hpos : (0 : ℝ) < (A.card : ℝ) * (B.card : ℝ) := mul_pos hApos hBpos
    nlinarith [mul_pos hApos hBpos]
  have hlt : ‖∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
      ψ c * (dft (indF A) ψ * dft (indF B) ψ)‖ ^ 2 < ((A.card : ℝ) * (B.card : ℝ)) ^ 2 :=
    lt_of_le_of_lt hcs hprod
  nlinarith [norm_nonneg (∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
      ψ c * (dft (indF A) ψ * dft (indF B) ψ)), mul_pos hApos hBpos]
