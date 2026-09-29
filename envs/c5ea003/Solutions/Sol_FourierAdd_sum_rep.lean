-- Prove2me | solution 1 for FourierAdd.sum_rep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:02:30.7866+00:00
-- url     : https://prove2.me/submissions/319f9e4f-3585-4cfd-babe-c15b3f3be458

-- Sol generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
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
theorem solution(A B : Finset G) : ∑ c : G, rep A B c = A.card * B.card := by
  have h1 : ∀ c : G, rep A B c = ∑ y ∈ A, if c - y ∈ B then 1 else 0 := by
    intro c
    rw [rep, Finset.card_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y : G, ∑ c : G, (if c - y ∈ B then 1 else 0) = B.card := by
    intro y
    rw [← Equiv.sum_comp (Equiv.addRight y) (fun c => if c - y ∈ B then 1 else 0)]
    have h3 : ∀ c : G, (if (Equiv.addRight y) c - y ∈ B then 1 else 0)
        = if c ∈ B then 1 else 0 := by
      intro c
      have : (Equiv.addRight y) c - y = c := by
        show c + y - y = c
        abel
      rw [this]
    simp_rw [h3]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  simp_rw [h2]
  rw [Finset.sum_const, smul_eq_mul]
