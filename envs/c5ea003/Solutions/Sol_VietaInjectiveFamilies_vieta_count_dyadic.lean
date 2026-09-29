-- Prove2me | solution 1 for VietaInjectiveFamilies.vieta_count_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:36:53.91454+00:00
-- url     : https://prove2.me/submissions/6cc88565-9536-4841-bf55-4413c587b844

-- Sol generated from NumberTheory/VietaInjectiveFamilies.lean
import Mathlib
import Definitions.Def_NumberTheory_VietaInjectiveFamilies
import Theorems.Thm_VietaInjectiveFamilies_dyadNat_inj

/-!
# Injective subfamilies of the Vieta three-cube identity

The Vieta identity `a³ + b³ + (-a-b)³ = -3ab(a+b)` produces, for every pair of
integers `(a, b)`, an integer which is a sum of three cubes.  This file studies
the *value map* `vietaValue a b = -3ab(a+b)` of that identity from the point of
view of injectivity and of quantitative counting:

* the exact six-element symmetry group of the value map (`vietaValue_symm_*`),
  which is the structural reason why the map is never injective on all of `ℤ²`;
* a residual collision *inside* the fundamental domain `1 ≤ a ≤ b`
  (`vieta_not_injOn_fundamental_domain`), showing that no ordering restriction
  alone can produce injectivity;
* a divisor bound for the multiplicity of a value
  (`vieta_multiplicity_le_card_divisors`), which is the arithmetic mechanism
  behind those collisions;
* two genuinely injective subfamilies:
  the *spine* `a = 1` (`spineNat_strictMono`) and the two-parameter
  *dyadic family* `a = 2^i`, `b` odd (`dyadNat_inj`), whose injectivity is
  proved via the `2`-adic valuation;
* quantitative lower bounds for the number of positive integers `≤ N` produced
  by the identity, all of them with **three nonzero cubes** (no padded `0³`):
  `vieta_count_ge_sqrt` gives `⌊√(N/6)⌋` and `vieta_count_dyadic` gives a
  two-parameter count `I * m`.

Everything is elementary but the counting statements are honest cardinality
statements about `Set.ncard` of the represented sets.
-/

open VietaInjectiveFamilies

/-! ## Basic definitions -/







/-! ## The symmetry group: why global injectivity is impossible -/









/-! ## Multiplicity of a Vieta value is bounded by its divisor count -/



/-! ## The represented set and its cardinality -/


theorem repSet_subset_Icc (N : ℕ) : repSet N ⊆ Set.Icc 1 (N : ℤ) := by
  rintro k ⟨hk0, hkN, -⟩
  exact ⟨hk0, hkN⟩

theorem repSet_finite (N : ℕ) : (repSet N).Finite :=
  (Set.finite_Icc (1 : ℤ) (N : ℤ)).subset (repSet_subset_Icc N)


/-- A finite set of witnesses gives a lower bound for `(repSet N).ncard`. -/
theorem card_le_ncard_repSet {N : ℕ} (T : Finset ℤ) (hT : ∀ k ∈ T, k ∈ repSet N) :
    T.card ≤ (repSet N).ncard := by
  have hsub : (↑T : Set ℤ) ⊆ repSet N := fun k hk => hT k (by simpa using hk)
  have := Set.ncard_le_ncard hsub (repSet_finite N)
  simpa [Set.ncard_coe_finset] using this

/-! ## The spine `a = 1` -/







/-! ## Both signs at once -/




/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/


theorem dyadNat_vietaRepresented (i b : ℕ) (hb : 1 ≤ b) :
    VietaRepresented (dyadNat i b : ℤ) := by
  have h2 : (0 : ℤ) < 2 ^ i := by positivity
  have hbz : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
  refine ⟨-(2 ^ i : ℤ), -(b : ℤ), ?_, ?_, ?_, ?_⟩
  · intro h; rw [neg_eq_zero] at h; exact absurd h h2.ne'
  · intro h; rw [neg_eq_zero] at h; linarith
  · intro h; linarith
  · unfold vietaValue dyadNat
    push_cast
    ring





open VietaInjectiveFamilies in
theorem solution(I m : ℕ) :
    I * m ≤ (repSet (6 * 2 ^ I * m * (2 ^ I + 2 * m))).ncard := by
  classical
  set N : ℕ := 6 * 2 ^ I * m * (2 ^ I + 2 * m) with hN
  set F : ℕ × ℕ → ℤ := fun p => (dyadNat p.1 (2 * p.2 + 1) : ℤ) with hF
  set S : Finset (ℕ × ℕ) := Finset.Icc 1 I ×ˢ Finset.range m with hS
  set T : Finset ℤ := S.image F with hT
  have hinj : Set.InjOn F ↑S := by
    rintro ⟨i, p⟩ hip ⟨j, q⟩ hjq hEq
    simp only [hS, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc,
      Finset.mem_range] at hip hjq
    simp only [hF] at hEq
    have h : dyadNat i (2 * p + 1) = dyadNat j (2 * q + 1) := by
      exact_mod_cast hEq
    obtain ⟨hij, hbc⟩ := dyadNat_inj hip.1.1 hjq.1.1 ⟨p, by ring⟩ ⟨q, by ring⟩
      (by omega) (by omega) h
    simp only [Prod.mk.injEq]
    exact ⟨hij, by omega⟩
  have hcard : T.card = I * m := by
    rw [hT, Finset.card_image_of_injOn hinj, hS, Finset.card_product,
      Nat.card_Icc, Finset.card_range]
    congr 1
  have hmem : ∀ k ∈ T, k ∈ repSet N := by
    intro k hk
    rw [hT, Finset.mem_image] at hk
    obtain ⟨⟨i, p⟩, hip, rfl⟩ := hk
    simp only [hS, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hip
    obtain ⟨⟨hi1, hiI⟩, hp⟩ := hip
    simp only [hF]
    refine ⟨?_, ?_, dyadNat_vietaRepresented i (2 * p + 1) (by omega)⟩
    · have : 0 < dyadNat i (2 * p + 1) := by
        unfold dyadNat; positivity
      exact_mod_cast this
    · have hb : 2 * p + 1 ≤ 2 * m := by omega
      have hpow : (2 : ℕ) ^ i ≤ 2 ^ I := Nat.pow_le_pow_right (by norm_num) hiI
      have : dyadNat i (2 * p + 1) ≤ N := by
        unfold dyadNat
        rw [hN]
        have h1 : 3 * 2 ^ i ≤ 3 * 2 ^ I := by omega
        have h2 : 3 * 2 ^ i * (2 * p + 1) ≤ 3 * 2 ^ I * (2 * m) :=
          Nat.mul_le_mul h1 hb
        have h3 : 2 ^ i + (2 * p + 1) ≤ 2 ^ I + 2 * m := by omega
        calc 3 * 2 ^ i * (2 * p + 1) * (2 ^ i + (2 * p + 1))
            ≤ 3 * 2 ^ I * (2 * m) * (2 ^ I + 2 * m) := Nat.mul_le_mul h2 h3
          _ = 6 * 2 ^ I * m * (2 ^ I + 2 * m) := by ring
      exact_mod_cast this
  calc I * m = T.card := hcard.symm
    _ ≤ (repSet N).ncard := card_le_ncard_repSet T hmem
