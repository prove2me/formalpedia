-- Prove2me | solution 1 for EtaHead.jet_etaQuotientProd
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:47:59.273141+00:00
-- url     : https://prove2.me/submissions/8efd7454-12e5-4e90-9db9-60857e891706

import Mathlib
import Definitions.Def_Tropical_EtaQuotientHeadCoeff

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Tropical/EtaQuotientHeadCoeff.lean ====
/-!
# The head coefficient of a normalised eta quotient

Let `a : ℕ → ℤ` be finitely supported (all our statements only use `a` on a finite
window, so finiteness is encoded by the truncation parameter `N`) and put

* `bCoeff a m = ∑_{k ∣ m} a k`,
* `etaQuotientProd a N = ∏_{m = 1}^{N} (1 - X^m)^{-bCoeff a m}`  (a unit of `ℤ⟦X⟧`).

If `∑ k · a k = 24` then the eta quotient `η_a = ∏_k η(kτ)^{a k}` satisfies
`η_a = q · ∏_m (1 - q^m)^{b m}`, hence

  `q / η_a = ∏_m (1 - q^m)^{-b m} = ∑_{n ≥ 0} c(n-1) qⁿ`,

so that in the usual "Hauptmodul" indexing `1/η_a = q^{-1} + c(0) + c(1) q + ⋯`
the head coefficient `c(1)` is the coefficient of `q²` in the product.

The main theorem `coeff_two_etaQuotientProd` proves

  `c(1) = a₁(a₁+3)/2 + a₂`,

for every truncation `N ≥ 2` (in particular the value is independent of `N`, which
is exactly the statement that the infinite product is well defined in degree `≤ 2`).

The proof is organised through a small amount of *2-jet* machinery: the group
homomorphism-like calculus of the coefficients in degrees `≤ 2` of units of `ℤ⟦X⟧`
with constant term `1` (`Jet`, `Jet.mul`, `Jet.inv`, `Jet.zpow`).

Further results in this file:

* `coeff_one_etaQuotientProd` : `c(0) = a₁`.
* `constantCoeff_etaQuotientProd` : the product is normalised, `c(-1) = 1`.
* `coeff_two_etaQuotientProd_stable` : the value of `c(1)` does not depend on the
  truncation `N ≥ 2`.

Companion files:

* `Tropical.EtaQuotientHeadStructure` : the Heisenberg cocycle `headCoeff_add`,
  the divisor regrouping `eta_regrouping_jet`, the Diophantine characterisation
  `pure_headCoeff_iff_sq`, surjectivity `headCoeff_surjective`, and the classical
  value `324` for `1/Δ` (`coeff_two_delta`).
* `Tropical.EtaQuotientSecondCoeff` : the 3-jet calculus and the closed form for
  `c(2)`.
* `Tropical.EtaQuotientStability` : all coefficients stabilise in the truncation.
-/

namespace EtaHead

open PowerSeries Finset

/-! ## Triangular numbers on `ℤ` -/

-- [dropped: platform already declares Tri]
lemma two_mul_Tri (n : ℤ) : 2 * Tri n = n * (n - 1) := by
  have h : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he; exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ := ho; exact ⟨n * k, by rw [hk]; ring⟩
  unfold Tri
  omega

lemma Tri_zero : Tri 0 = 0 := by unfold Tri; decide

lemma Tri_succ (n : ℤ) : Tri (n + 1) = Tri n + n := by
  have h1 := two_mul_Tri (n + 1)
  have h2 := two_mul_Tri n
  have : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by ring
  omega

lemma Tri_pred (n : ℤ) : Tri (n - 1) = Tri n - (n - 1) := by
  have := Tri_succ (n - 1)
  have h : n - 1 + 1 = n := by ring
  rw [h] at this
  omega

/-! ## 2-jets of power series -/

-- [dropped: platform already declares Jet]
lemma coeff_one_mul (f g : PowerSeries ℤ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul]; simp [Finset.antidiagonal]

lemma coeff_two_mul (f g : PowerSeries ℤ) :
    coeff 2 (f * g) =
      coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  rw [coeff_mul]; simp [Finset.antidiagonal]; ring

lemma Jet.one : Jet 1 0 0 := by
  refine ⟨by simp, ?_, ?_⟩ <;> simp [PowerSeries.coeff_one]

lemma Jet.mul {f g : PowerSeries ℤ} {c1 c2 d1 d2 : ℤ}
    (hf : Jet f c1 c2) (hg : Jet g d1 d2) :
    Jet (f * g) (c1 + d1) (c2 + c1 * d1 + d2) := by
  obtain ⟨hf0, hf1, hf2⟩ := hf
  obtain ⟨hg0, hg1, hg2⟩ := hg
  rw [← coeff_zero_eq_constantCoeff_apply] at hf0 hg0
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mul]
    simp [Finset.antidiagonal, hf0, hg0]
  · rw [coeff_one_mul, hf0, hg0, hf1, hg1]; ring
  · rw [coeff_two_mul, hf0, hg0, hf1, hg1, hf2, hg2]; ring

lemma Jet.inv {u : (PowerSeries ℤ)ˣ} {c1 c2 : ℤ} (hu : Jet (u : PowerSeries ℤ) c1 c2) :
    Jet ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (-c1) (c1 ^ 2 - c2) := by
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hmul : (u : PowerSeries ℤ) * (u⁻¹ : (PowerSeries ℤ)ˣ) = 1 := u.mul_inv
  have h0 : constantCoeff ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    have := congrArg constantCoeff hmul
    rw [map_mul, hu0, map_one, one_mul] at this
    exact this
  have hu0' : coeff 0 (u : PowerSeries ℤ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact hu0
  have h0' : coeff 0 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0
  have e1 : coeff 1 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = -c1 := by
    have := congrArg (fun f => coeff 1 f) hmul
    simp only [coeff_one_mul, hu0', h0', hu1] at this
    simp [PowerSeries.coeff_one] at this
    linarith
  have e2 : coeff 2 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = c1 ^ 2 - c2 := by
    have := congrArg (fun f => coeff 2 f) hmul
    simp only [coeff_two_mul, hu0', h0', hu1, hu2, e1] at this
    simp [PowerSeries.coeff_one] at this
    nlinarith [this]
  exact ⟨h0, e1, e2⟩

lemma Jet.zpow {u : (PowerSeries ℤ)ˣ} {c1 c2 : ℤ} (hu : Jet (u : PowerSeries ℤ) c1 c2) :
    ∀ n : ℤ, Jet ((u ^ n : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (n * c1) (n * c2 + Tri n * c1 ^ 2) := by
  intro n
  induction n using Int.induction_on with
  | zero => simpa [Tri_zero] using (Jet.one)
  | succ k ih =>
      have hstep := ih.mul hu
      have hcast : ((k : ℤ) + 1) * c1 = (k : ℤ) * c1 + c1 := by ring
      have hcast2 : ((k : ℤ) + 1) * c2 + Tri ((k : ℤ) + 1) * c1 ^ 2
          = ((k : ℤ) * c2 + Tri (k : ℤ) * c1 ^ 2) + ((k : ℤ) * c1) * c1 + c2 := by
        rw [Tri_succ]; ring
      rw [zpow_add_one, Units.val_mul, hcast, hcast2]
      exact hstep
  | pred k ih =>
      have hstep := ih.mul hu.inv
      have hcast : (-(k : ℤ) - 1) * c1 = (-(k : ℤ)) * c1 + -c1 := by ring
      have hcast2 : (-(k : ℤ) - 1) * c2 + Tri (-(k : ℤ) - 1) * c1 ^ 2
          = ((-(k : ℤ)) * c2 + Tri (-(k : ℤ)) * c1 ^ 2) + ((-(k : ℤ)) * c1) * (-c1)
            + (c1 ^ 2 - c2) := by
        rw [Tri_pred]; ring
      rw [zpow_sub_one, Units.val_mul, hcast, hcast2]
      exact hstep

lemma Jet.prod_trivial {ι : Type*} {s : Finset ι} {f : ι → PowerSeries ℤ}
    (h : ∀ i ∈ s, Jet (f i) 0 0) : Jet (∏ i ∈ s, f i) 0 0 := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Jet.one
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have h1 : Jet (f i) 0 0 := h i (by simp)
      have h2 : Jet (∏ j ∈ s, f j) 0 0 := ih fun j hj => h j (by simp [hj])
      simpa using h1.mul h2

lemma Jet.zpow_trivial {u : (PowerSeries ℤ)ˣ} (hu : Jet (u : PowerSeries ℤ) 0 0) (n : ℤ) :
    Jet ((u ^ n : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 0 := by
  have h := hu.zpow n
  have h2 : n * (0 : ℤ) + Tri n * (0 : ℤ) ^ 2 = 0 := by ring
  rw [h2] at h
  have h1 : n * (0 : ℤ) = 0 := by ring
  rw [h1] at h
  exact h

lemma Jet.mul_left_trivial {f g : PowerSeries ℤ} {c1 c2 : ℤ}
    (hf : Jet f 0 0) (hg : Jet g c1 c2) : Jet (f * g) c1 c2 := by
  have h := hf.mul hg
  have h1 : (0 : ℤ) + c1 = c1 := by ring
  have h2 : (0 : ℤ) + 0 * c1 + c2 = c2 := by ring
  rw [h1, h2] at h
  exact h

lemma Jet.mul_right_trivial {f g : PowerSeries ℤ} {c1 c2 : ℤ}
    (hf : Jet f c1 c2) (hg : Jet g 0 0) : Jet (f * g) c1 c2 := by
  have h := hf.mul hg
  have h1 : c1 + (0 : ℤ) = c1 := by ring
  have h2 : c2 + c1 * (0 : ℤ) + 0 = c2 := by ring
  rw [h1, h2] at h
  exact h

lemma Jet.prod_units_trivial {ι : Type*} {s : Finset ι} {u : ι → (PowerSeries ℤ)ˣ}
    (h : ∀ i ∈ s, Jet ((u i : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 0) :
    Jet ((∏ i ∈ s, u i : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 0 := by
  rw [Units.coe_prod]
  exact Jet.prod_trivial h

/-! ## The basic units `1 - X^m` -/

-- [dropped: platform already declares isUnit_one_sub_X_pow]
-- [dropped: platform already declares oneSubXPow]
lemma coe_oneSubXPow {m : ℕ} (hm : 1 ≤ m) :
    ((oneSubXPow m : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 - X ^ m := by
  rw [oneSubXPow, dif_pos hm]
  rfl

lemma coeff_one_sub_X_pow (j m : ℕ) :
    coeff j (1 - X ^ m : PowerSeries ℤ)
      = (if j = 0 then 1 else 0) - (if j = m then 1 else 0) := by
  rw [map_sub, coeff_X_pow]
  simp [PowerSeries.coeff_one]

lemma jet_oneSubXPow_one : Jet ((oneSubXPow 1 : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (-1) 0 := by
  rw [coe_oneSubXPow (le_refl 1)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_one_sub_X_pow 0 1]; norm_num
  · rw [coeff_one_sub_X_pow 1 1]; norm_num
  · rw [coeff_one_sub_X_pow 2 1]; norm_num

lemma jet_oneSubXPow_two : Jet ((oneSubXPow 2 : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 (-1) := by
  rw [coe_oneSubXPow (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_one_sub_X_pow 0 2]; norm_num
  · rw [coeff_one_sub_X_pow 1 2]; norm_num
  · rw [coeff_one_sub_X_pow 2 2]; norm_num

lemma jet_oneSubXPow_ge_three {m : ℕ} (hm : 3 ≤ m) :
    Jet ((oneSubXPow m : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 0 := by
  have hm1 : 1 ≤ m := by omega
  rw [coe_oneSubXPow hm1]
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_one_sub_X_pow 0 m]
    have : ¬ (0 = m) := by omega
    simp [this]
  · rw [coeff_one_sub_X_pow 1 m]
    have : ¬ (1 = m) := by omega
    simp [this]
  · rw [coeff_one_sub_X_pow 2 m]
    have : ¬ (2 = m) := by omega
    simp [this]

/-! ## Divisor sums and the eta quotient product -/

-- [dropped: platform already declares bCoeff]
lemma bCoeff_one (a : ℕ → ℤ) : bCoeff a 1 = a 1 := by
  simp [bCoeff]

lemma bCoeff_two (a : ℕ → ℤ) : bCoeff a 2 = a 1 + a 2 := by
  have : (2 : ℕ).divisors = {1, 2} := by decide
  rw [bCoeff, this]
  simp

-- [dropped: platform already declares etaQuotientProd]
-- [dropped: platform already declares headCoeff]
lemma two_mul_headCoeff (a : ℕ → ℤ) : 2 * headCoeff a = a 1 * (a 1 + 3) + 2 * a 2 := by
  have h : (2 : ℤ) ∣ a 1 * (a 1 + 3) := by
    rcases Int.even_or_odd (a 1) with he | ho
    · obtain ⟨k, hk⟩ := he; exact ⟨k * (a 1 + 3), by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ := ho; exact ⟨(2 * k + 1) * (k + 2), by rw [hk]; ring⟩
  unfold headCoeff
  omega

/-- The 2-jet of the truncated eta quotient: for every truncation `N ≥ 2` the
coefficients in degrees `1` and `2` are `a₁` and `headCoeff a`. -/
theorem jet_etaQuotientProd (a : ℕ → ℤ) {N : ℕ} (hN : 2 ≤ N) :
    Jet ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (a 1) (headCoeff a) := by
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge N 2 with hlt | hge
      · -- base case `N + 1 = 2`
        have hN2 : N = 1 := by omega
        subst hN2
        have hIcc : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
        rw [etaQuotientProd, hIcc, Finset.prod_insert (by decide), Finset.prod_singleton,
          Units.val_mul]
        have hmul := (jet_oneSubXPow_one.zpow (-(bCoeff a 1))).mul
          (jet_oneSubXPow_two.zpow (-(bCoeff a 2)))
        have e1 : -(bCoeff a 1) * (-1 : ℤ) + -(bCoeff a 2) * 0 = a 1 := by
          rw [bCoeff_one]; ring
        have e2 : (-(bCoeff a 1) * 0 + Tri (-(bCoeff a 1)) * (-1 : ℤ) ^ 2)
              + (-(bCoeff a 1) * (-1 : ℤ)) * (-(bCoeff a 2) * 0)
              + (-(bCoeff a 2) * (-1) + Tri (-(bCoeff a 2)) * 0 ^ 2) = headCoeff a := by
          have hT := two_mul_Tri (-(bCoeff a 1))
          have hH := two_mul_headCoeff a
          rw [bCoeff_one] at hT ⊢
          rw [bCoeff_two]
          have h3 : (-(a 1)) * (-(a 1) - 1) = a 1 * (a 1 + 1) := by ring
          rw [h3] at hT
          have hexp : a 1 * (a 1 + 3) = a 1 * (a 1 + 1) + 2 * a 1 := by ring
          omega
        rw [e1, e2] at hmul
        exact hmul
      · -- inductive step: the new factor is trivial modulo `X³`
        have hih : Jet ((∏ m ∈ Icc 1 N, (oneSubXPow m) ^ (-(bCoeff a m)) :
            (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (a 1) (headCoeff a) := ih (by omega)
        have hins : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) :=
          (Finset.insert_Icc_right_eq_Icc_add_one (by omega)).symm
        rw [etaQuotientProd, hins, Finset.prod_insert (by simp), Units.val_mul]
        have hnew := (jet_oneSubXPow_ge_three (m := N + 1) (by omega)).zpow (-(bCoeff a (N + 1)))
        have hcomb := hnew.mul hih
        have g1 : -(bCoeff a (N + 1)) * (0 : ℤ) + a 1 = a 1 := by ring
        have g2 : (-(bCoeff a (N + 1)) * (0 : ℤ) + Tri (-(bCoeff a (N + 1))) * 0 ^ 2)
            + (-(bCoeff a (N + 1)) * (0 : ℤ)) * (a 1) + headCoeff a = headCoeff a := by ring
        rw [g1, g2] at hcomb
        exact hcomb

/-- **Main theorem.**  The head coefficient of the eta quotient:
`c(1) = a₁(a₁+3)/2 + a₂`, independently of the truncation `N ≥ 2`. -/
theorem coeff_two_etaQuotientProd (a : ℕ → ℤ) {N : ℕ} (hN : 2 ≤ N) :
    coeff 2 ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      = a 1 * (a 1 + 3) / 2 + a 2 :=
  (jet_etaQuotientProd a hN).2.2

/-- `c(0) = a₁`: the constant term of `q/η_a`. -/
theorem coeff_one_etaQuotientProd (a : ℕ → ℤ) {N : ℕ} (hN : 2 ≤ N) :
    coeff 1 ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = a 1 :=
  (jet_etaQuotientProd a hN).2.1

/-- The product is normalised: constant term `1`. -/
theorem constantCoeff_etaQuotientProd (a : ℕ → ℤ) {N : ℕ} (hN : 2 ≤ N) :
    constantCoeff ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 :=
  (jet_etaQuotientProd a hN).1

/-- Stability in the truncation: the degree `≤ 2` part does not depend on `N ≥ 2`,
which is the precise sense in which the infinite product is well defined here. -/
theorem coeff_two_etaQuotientProd_stable (a : ℕ → ℤ) {N M : ℕ} (hN : 2 ≤ N) (hM : 2 ≤ M) :
    coeff 2 ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      = coeff 2 ((etaQuotientProd a M : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
  rw [coeff_two_etaQuotientProd a hN, coeff_two_etaQuotientProd a hM]

end EtaHead
section
open EtaHead
open PowerSeries Finset

theorem solution (a : ℕ → ℤ) {N : ℕ} (hN : 2 ≤ N) :
    Jet ((etaQuotientProd a N : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (a 1) (headCoeff a) :=
  @EtaHead.jet_etaQuotientProd a N hN

end
