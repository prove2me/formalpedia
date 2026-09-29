-- Prove2me | solution 1 for FourierAdd.card_support_rep_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:04:07.361473+00:00
-- url     : https://prove2.me/submissions/178ad5cf-16a5-4f9b-992a-0c68c3f01f48

-- Sol generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierAdd_energy_identity
import Theorems.Thm_FourierAdd_sum_rep
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
theorem solution(A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (Fintype.card G : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) ^ 2
        / (((A.card : ℝ) * (B.card : ℝ)) ^ 2
          + ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
              ‖dft (indF A) ψ‖ ^ 2 * ‖dft (indF B) ψ‖ ^ 2)
      ≤ ((Finset.univ : Finset G).filter (fun c => 0 < rep A B c)).card := by
  set T := (Finset.univ : Finset G).filter (fun c => 0 < rep A B c) with hT
  set E := ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
      ‖dft (indF A) ψ‖ ^ 2 * ‖dft (indF B) ψ‖ ^ 2 with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun ψ _ => by positivity
  have hcardpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  -- the representation function is supported on `T`
  have hsupp1 : ∑ c ∈ T, (rep A B c : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
    have h0 : ∑ c ∈ T, (rep A B c : ℝ) = ∑ c : G, (rep A B c : ℝ) := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro c _ hc
      have : rep A B c = 0 := by
        by_contra h
        exact hc (Finset.mem_filter.2 ⟨Finset.mem_univ c, Nat.pos_of_ne_zero h⟩)
      rw [this]
      norm_num
    rw [h0]
    have := sum_rep A B
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
  have hsupp2 : ∑ c ∈ T, ((rep A B c : ℝ)) ^ 2 = ∑ c : G, ((rep A B c : ℝ)) ^ 2 := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro c _ hc
    have : rep A B c = 0 := by
      by_contra h
      exact hc (Finset.mem_filter.2 ⟨Finset.mem_univ c, Nat.pos_of_ne_zero h⟩)
    rw [this]
    norm_num
  -- Cauchy–Schwarz on `T`
  have hcs : ((A.card : ℝ) * (B.card : ℝ)) ^ 2
      ≤ (T.card : ℝ) * ∑ c : G, ((rep A B c : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun c => (rep A B c : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hsupp1, hsupp2] at h
    exact h
  -- combine with the energy identity
  have henergy := energy_identity A B
  rw [← hE] at henergy
  have hsum : ∑ c : G, ((rep A B c : ℝ)) ^ 2
      = (((A.card : ℝ) * (B.card : ℝ)) ^ 2 + E) / (Fintype.card G : ℝ) := by
    field_simp at henergy ⊢
    linarith [henergy]
  rw [hsum] at hcs
  have hden : (0 : ℝ) < ((A.card : ℝ) * (B.card : ℝ)) ^ 2 + E := by positivity
  rw [div_le_iff₀ hden]
  have hstep : ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * (Fintype.card G : ℝ)
      ≤ (T.card : ℝ) * (((A.card : ℝ) * (B.card : ℝ)) ^ 2 + E) := by
    have := mul_le_mul_of_nonneg_left hcs (le_of_lt hcardpos)
    calc ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * (Fintype.card G : ℝ)
        = (Fintype.card G : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) ^ 2 := by ring
      _ ≤ (Fintype.card G : ℝ) * ((T.card : ℝ)
            * ((((A.card : ℝ) * (B.card : ℝ)) ^ 2 + E) / (Fintype.card G : ℝ))) := this
      _ = (T.card : ℝ) * (((A.card : ℝ) * (B.card : ℝ)) ^ 2 + E) := by
          field_simp
  linarith [hstep]
