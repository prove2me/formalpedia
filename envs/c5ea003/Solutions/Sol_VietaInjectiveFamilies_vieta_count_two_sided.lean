-- Prove2me | solution 1 for VietaInjectiveFamilies.vieta_count_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:36:54.88344+00:00
-- url     : https://prove2.me/submissions/f6e30fc8-b35c-4340-9251-806e2dda40cc

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






/-- The Vieta family is closed under simultaneous sign change. -/
theorem vietaValue_neg (a b : ℤ) : vietaValue (-a) (-b) = -vietaValue a b := by
  unfold vietaValue; ring

/-! ## The symmetry group: why global injectivity is impossible -/









/-! ## Multiplicity of a Vieta value is bounded by its divisor count -/



/-! ## The represented set and its cardinality -/






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


theorem absRepSet_finite (N : ℕ) : (absRepSet N).Finite := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  rintro k ⟨-, hk, -⟩
  exact ⟨neg_le_of_abs_le hk, le_of_abs_le hk⟩


/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/







open VietaInjectiveFamilies in
theorem solution(N m : ℕ) (h : 3 * m * (m + 1) ≤ N) :
    2 * m ≤ (absRepSet N).ncard := by
  classical
  set Tp : Finset ℤ := (Finset.Icc 1 m).image (fun b : ℕ => (spineNat b : ℤ)) with hTp
  set Tn : Finset ℤ := (Finset.Icc 1 m).image (fun b : ℕ => -(spineNat b : ℤ)) with hTn
  have hinjp : Function.Injective (fun b : ℕ => (spineNat b : ℤ)) := by
    intro b c hbc
    simp only [Nat.cast_inj] at hbc
    exact spineNat_injective hbc
  have hinjn : Function.Injective (fun b : ℕ => -(spineNat b : ℤ)) := by
    intro b c hbc
    simp only [neg_inj, Nat.cast_inj] at hbc
    exact spineNat_injective hbc
  have hpos : ∀ b : ℕ, 1 ≤ b → 0 < (spineNat b : ℤ) := by
    intro b hb
    have : 0 < spineNat b := by unfold spineNat; nlinarith [hb]
    exact_mod_cast this
  have hdisj : Disjoint Tp Tn := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk hk'
    rw [hTp, Finset.mem_image] at hk
    rw [hTn, Finset.mem_image] at hk'
    obtain ⟨b, hb, rfl⟩ := hk
    obtain ⟨c, hc, hce⟩ := hk'
    rw [Finset.mem_Icc] at hb hc
    have h1 := hpos b hb.1
    have h2 := hpos c hc.1
    omega
  have hcard : (Tp ∪ Tn).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hdisj, hTp, hTn,
      Finset.card_image_of_injective _ hinjp,
      Finset.card_image_of_injective _ hinjn, Nat.card_Icc]
    omega
  have hmem : ∀ k ∈ Tp ∪ Tn, k ∈ absRepSet N := by
    intro k hk
    have hbound : ∀ b : ℕ, b ≤ m → (spineNat b : ℤ) ≤ (N : ℤ) := by
      intro b hb
      have hle : spineNat b ≤ spineNat m := spineNat_strictMono.monotone hb
      have : spineNat m ≤ N := by unfold spineNat at *; omega
      exact_mod_cast le_trans hle this
    rw [Finset.mem_union] at hk
    rcases hk with hk | hk
    · rw [hTp, Finset.mem_image] at hk
      obtain ⟨b, hb, rfl⟩ := hk
      rw [Finset.mem_Icc] at hb
      have h1 := hpos b hb.1
      refine ⟨by omega, ?_, spineNat_vietaRepresented hb.1⟩
      rw [abs_of_pos h1]
      exact hbound b hb.2
    · rw [hTn, Finset.mem_image] at hk
      obtain ⟨b, hb, rfl⟩ := hk
      rw [Finset.mem_Icc] at hb
      have h1 := hpos b hb.1
      refine ⟨by omega, ?_, ?_⟩
      · rw [abs_of_neg (by omega : -(spineNat b : ℤ) < 0), neg_neg]
        exact hbound b hb.2
      · obtain ⟨a, c, ha, hc, hac, hval⟩ := spineNat_vietaRepresented hb.1
        refine ⟨-a, -c, by simpa using ha, by simpa using hc, ?_, ?_⟩
        · intro h0
          exact hac (by linarith)
        · rw [vietaValue_neg, hval]
  calc 2 * m = (Tp ∪ Tn).card := hcard.symm
    _ ≤ (absRepSet N).ncard := by
        have hsub : (↑(Tp ∪ Tn) : Set ℤ) ⊆ absRepSet N :=
          fun k hk => hmem k (by simpa using hk)
        have hle := Set.ncard_le_ncard hsub (absRepSet_finite N)
        rwa [Set.ncard_coe_finset] at hle
