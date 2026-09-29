-- Prove2me | solution 1 for VietaInjectiveFamilies.vieta_count_spine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:36:54.375054+00:00
-- url     : https://prove2.me/submissions/0a01e729-ef67-4c96-8585-472e8c781992

-- Sol generated from NumberTheory/VietaInjectiveFamilies.lean
import Mathlib
import Definitions.Def_NumberTheory_VietaInjectiveFamilies

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


theorem spineNat_strictMono : StrictMono spineNat := by
  intro b c hbc
  unfold spineNat
  nlinarith

theorem spineNat_injective : Function.Injective spineNat :=
  spineNat_strictMono.injective

/-- The spine values are Vieta represented, with three nonzero cubes. -/
theorem spineNat_vietaRepresented {b : ℕ} (hb : 1 ≤ b) :
    VietaRepresented (spineNat b : ℤ) := by
  refine ⟨-1, -(b : ℤ), by norm_num, ?_, ?_, ?_⟩
  · simpa using (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hb : (b : ℤ) ≠ 0)
  · have : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    intro h; linarith
  · unfold vietaValue spineNat
    push_cast
    ring



/-! ## Both signs at once -/




/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/







open VietaInjectiveFamilies in
theorem solution(N m : ℕ) (h : 3 * m * (m + 1) ≤ N) :
    m ≤ (repSet N).ncard := by
  classical
  set T : Finset ℤ := (Finset.Icc 1 m).image (fun b : ℕ => (spineNat b : ℤ)) with hT
  have hinj : Function.Injective (fun b : ℕ => (spineNat b : ℤ)) := by
    intro b c hbc
    simp only [Nat.cast_inj] at hbc
    exact spineNat_injective hbc
  have hcard : T.card = m := by
    rw [hT, Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  have hmem : ∀ k ∈ T, k ∈ repSet N := by
    intro k hk
    rw [hT, Finset.mem_image] at hk
    obtain ⟨b, hb, rfl⟩ := hk
    rw [Finset.mem_Icc] at hb
    refine ⟨?_, ?_, spineNat_vietaRepresented hb.1⟩
    · have : 0 < spineNat b := by unfold spineNat; nlinarith [hb.1]
      exact_mod_cast this
    · have hle : spineNat b ≤ spineNat m := spineNat_strictMono.monotone hb.2
      have : spineNat m ≤ N := by unfold spineNat at *; omega
      exact_mod_cast le_trans hle this
  calc m = T.card := hcard.symm
    _ ≤ (repSet N).ncard := card_le_ncard_repSet T hmem
