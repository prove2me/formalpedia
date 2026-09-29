-- Prove2me | solution 2 for mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T06:55:17.311464+00:00
-- url     : https://prove2.me/submissions/18feafca-4dc4-4013-813f-7f37ea254ce3

import Theorems.Thm_mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
import Mathlib.Tactic

open MME
set_option autoImplicit false

theorem solution :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E F : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              F ⊆ E ∧
              (∀ e ∈ F, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ F.image (fun e => e.1 2),
                H ≤ (F.filter (fun e => e.1 2 = c)).card) ∧
              (∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                ((F.image (fun e => e.1 2)).card : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  classical
  obtain ⟨d, hd, hfamily⟩ := mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
  refine ⟨d, hd, ?_⟩
  intro N L G hreg hprofile Zcount Xcount middle Mmod S hS hfree hpos
  obtain ⟨A, H, family, hHbound, hA, hmiddle⟩ :=
    hfamily N L G hreg hprofile S hS hfree hpos
  let F : Finset (CWQ6ExactCoupledAddress N L G) := Finset.univ.image family.entry
  have hentry : Function.Injective family.entry := by
    intro p q h
    exact family.xInjective (congrArg (fun e ↦ e.1 0) h)
  let hzero : Fin H := ⟨0, family.hHpos⟩
  let z : Fin A → (Fin (2 * N) → Fin 3) := fun a ↦ (family.entry (a, hzero)).1 2
  have hz : Function.Injective z := by
    intro a b h
    exact family.zSeparatesFibers a b hzero hzero h
  have himage : F.image (fun e ↦ e.1 2) = Finset.univ.image z := by
    ext c
    simp only [F, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, ⟨⟨a, h⟩, rfl⟩, rfl⟩
      exact ⟨a, (family.zSameFiber a hzero h)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨family.entry (a, hzero), ⟨(a, hzero), rfl⟩, rfl⟩
  have hcard : (F.image (fun e ↦ e.1 2)).card = A := by
    rw [himage, Finset.card_image_of_injective _ hz]
    simp
  refine ⟨F, F, H, family.hHpos, Finset.Subset.refl _, ?_, ?_, ?_, hHbound, ?_, hmiddle⟩
  · intro e he e' he' h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he'
    rcases h with h | h
    · exact congrArg family.entry (family.xInjective h)
    · exact congrArg family.entry (family.yInjective h)
  · intro c hc
    rw [himage] at hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    let fiber : Finset (CWQ6ExactCoupledAddress N L G) :=
      Finset.univ.image (fun h : Fin H ↦ family.entry (a, h))
    have hfcard : fiber.card = H := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro h k heq
        exact congrArg Prod.snd (hentry heq)
    rw [← hfcard]
    apply Finset.card_le_card
    intro e he
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨(a, h), Finset.mem_univ _, rfl⟩,
      family.zSameFiber a h hzero⟩
  · intro ex hx ey hy ez hz hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hpq, hpr⟩ := family.induced p q r hs
    refine ⟨family.entry p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩,
      rfl, ?_, ?_⟩
    · rw [hpq]
    · rcases p with ⟨a, h⟩
      rcases r with ⟨b, k⟩
      dsimp only at hpr
      subst b
      exact family.zSameFiber a h k
  · simpa only [hcard] using hA


#print axioms solution
