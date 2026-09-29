-- Prove2me | solution 1 for VietaInjectiveFamilies.vieta_multiplicity_le_card_divisors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:36:55.502295+00:00
-- url     : https://prove2.me/submissions/b95d9d27-4266-4823-8a8b-2179860bc0bf

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

/-- For a fixed positive `a`, the map `b ↦ 3ab(a+b)` is strictly monotone. -/
theorem vieta_strictMono_snd {a : ℕ} (ha : 1 ≤ a) :
    StrictMono (fun b : ℕ => 3 * a * b * (a + b)) := by
  intro b c hbc
  have hlt : b * (a + b) < c * (a + c) := by nlinarith
  have h3a : 0 < 3 * a := by omega
  calc 3 * a * b * (a + b) = (3 * a) * (b * (a + b)) := by ring
    _ < (3 * a) * (c * (a + c)) := by exact Nat.mul_lt_mul_of_pos_left hlt h3a
    _ = 3 * a * c * (a + c) := by ring


/-! ## The represented set and its cardinality -/






/-! ## The spine `a = 1` -/







/-! ## Both signs at once -/




/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/







open VietaInjectiveFamilies in
theorem solution(v : ℕ) (hv : v ≠ 0) :
    (((Finset.Icc 1 v ×ˢ Finset.Icc 1 v).filter
        (fun p => 3 * p.1 * p.2 * (p.1 + p.2) = v)).card) ≤ v.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · rintro ⟨a, b⟩ hp
    obtain ⟨-, hval⟩ := Finset.mem_filter.mp hp
    have hval2 : 3 * a * b * (a + b) = v := hval
    refine Nat.mem_divisors.mpr ⟨⟨3 * b * (a + b), ?_⟩, hv⟩
    rw [← hval2]; ring
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' hEq
    obtain ⟨hmem, hval⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨-, hval'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
    have hval2 : 3 * a * b * (a + b) = v := hval
    have hval2' : 3 * a' * b' * (a' + b') = v := hval'
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem).1).1
    have haa : a = a' := hEq
    subst haa
    have hb : b = b' :=
      (vieta_strictMono_snd ha1).injective
        (show 3 * a * b * (a + b) = 3 * a * b' * (a + b') by rw [hval2, hval2'])
    rw [hb]
