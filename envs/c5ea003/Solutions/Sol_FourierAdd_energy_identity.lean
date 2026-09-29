-- Prove2me | solution 1 for FourierAdd.energy_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:02:30.040353+00:00
-- url     : https://prove2.me/submissions/064f6122-3e74-4876-b91a-2e199f625be2

-- Sol generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierFA_dft_conv
import Theorems.Thm_FourierFA_parseval_norm
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



/-- The convolution of two indicators is the representation-counting function. -/
theorem conv_indF (A B : Finset G) (c : G) :
    conv (indF A) (indF B) c = (rep A B c : ℂ) := by
  have h : ∀ y : G, indF A y * indF B (c - y)
      = if y ∈ A.filter (fun y => c - y ∈ B) then (1 : ℂ) else 0 := by
    intro y
    simp only [indF, Finset.mem_filter]
    by_cases h1 : y ∈ A <;> by_cases h2 : c - y ∈ B <;> simp [h1, h2]
  rw [conv]
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one, rep]

/-- The Fourier coefficient of an indicator at the trivial character is the cardinality. -/
@[simp] theorem dft_indF_zero (A : Finset G) : dft (indF A) 0 = (A.card : ℂ) := by
  rw [dft]
  have h : ∀ x : G, conj ((0 : AddChar G ℂ) x) * indF A x
      = if x ∈ A then (1 : ℂ) else 0 := by
    intro x
    simp [indF]
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]














open FourierAdd in
theorem solution(A B : Finset G) :
    (Fintype.card G : ℝ) * ∑ c : G, ((rep A B c : ℝ)) ^ 2
      = ((A.card : ℝ) * (B.card : ℝ)) ^ 2
        + ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
            ‖dft (indF A) ψ‖ ^ 2 * ‖dft (indF B) ψ‖ ^ 2 := by
  have hpar := parseval_norm (conv (indF A) (indF B))
  have hR : ∀ c : G, ‖conv (indF A) (indF B) c‖ ^ 2 = ((rep A B c : ℝ)) ^ 2 := by
    intro c
    rw [conv_indF, Complex.norm_natCast]
  have hL : ∀ ψ : AddChar G ℂ, ‖dft (conv (indF A) (indF B)) ψ‖ ^ 2
      = ‖dft (indF A) ψ‖ ^ 2 * ‖dft (indF B) ψ‖ ^ 2 := by
    intro ψ
    rw [dft_conv, norm_mul, mul_pow]
  simp_rw [hR, hL] at hpar
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar G ℂ))] at hpar
  rw [dft_indF_zero, dft_indF_zero, Complex.norm_natCast, Complex.norm_natCast] at hpar
  rw [← hpar]
  ring
