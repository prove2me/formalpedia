-- Prove2me | solution 1 for NewtonTropical.padicVal_add_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:04:02.623555+00:00
-- url     : https://prove2.me/submissions/7b5bc61d-34ee-491e-b79e-1cb753b1be28

-- Sol generated from Combinatorics/Newtontropicalbridge/NewtonTropicalBridge.lean
import Mathlib
import Definitions.Def_Combinatorics_Newtontropicalbridge_NewtonTropicalBridge

/-!
# The Newton–tropical bridge

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/NewtonTropicalBridge.lean`.  It is reconstructed here as
a self-contained account of the bridge between *`p`-adic valuations* (the data
recorded by a Newton polygon) and the *tropical (min-plus) semiring*.

The bridge is the statement that `v_p : ℕ_{>0} → ℕ` intertwines the ordinary
arithmetic operations with the tropical ones:

| ordinary | tropical |
|----------|----------|
| `a * b`  | `v a + v b`   (`padicVal_mul`) |
| `a + b`  | `min (v a) (v b)` (`min_le_padicVal_add`, with equality in `padicVal_add_of_ne`) |

Main results:

* `NewtonTropical.padicVal_mul` — multiplicativity;
* `NewtonTropical.min_le_padicVal_add` — the ultrametric (tropical) inequality;
* `NewtonTropical.padicVal_add_of_ne` — the *Newton polygon* phenomenon: the
  inequality is an equality whenever the two valuations differ;
* `NewtonTropical.padicVal_pow`, `NewtonTropical.padicVal_prod` — the tropical
  power and product rules;
* `NewtonTropical.newton_slope_min` — the lowest Newton slope of a two-term sum.
-/

open NewtonTropical

open Nat

variable {p : ℕ}


lemma pow_dvd_iff_le_val (hp : p.Prime) {n k : ℕ} (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ val p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  simpa [val] using padicValNat_dvd_iff_le hn

lemma pow_val_dvd (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) : p ^ val p n ∣ n :=
  (pow_dvd_iff_le_val hp hn).mpr le_rfl

/-! ## Tropical multiplication -/




/-! ## Tropical addition -/

/-- **The ultrametric (tropical addition) inequality**: `v (a + b) ≥ min (v a) (v b)`. -/
theorem min_le_padicVal_add (hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    min (val p a) (val p b) ≤ val p (a + b) := by
  have hab : a + b ≠ 0 := by omega
  rw [← pow_dvd_iff_le_val hp hab]
  refine Nat.dvd_add ?_ ?_
  · exact dvd_trans (pow_dvd_pow p (min_le_left _ _)) (pow_val_dvd hp ha)
  · exact dvd_trans (pow_dvd_pow p (min_le_right _ _)) (pow_val_dvd hp hb)




open NewtonTropical in
theorem solution(hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : val p a ≠ val p b) : val p (a + b) = min (val p a) (val p b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hab : a + b ≠ 0 := by omega
  refine le_antisymm ?_ (min_le_padicVal_add hp ha hb)
  -- WLOG `val p a < val p b`
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [min_eq_left hlt.le]
    by_contra hcon
    push_neg at hcon
    -- then `p ^ (val a + 1)` divides both `a + b` and `b`, hence `a`
    have h1 : p ^ (val p a + 1) ∣ (a + b) := (pow_dvd_iff_le_val hp hab).mpr hcon
    have h2 : p ^ (val p a + 1) ∣ b :=
      dvd_trans (pow_dvd_pow p hlt) (pow_val_dvd hp hb)
    have h3 : p ^ (val p a + 1) ∣ a := by
      have := Nat.dvd_sub h1 h2
      simpa using this
    exact absurd ((pow_dvd_iff_le_val hp ha).mp h3) (by omega)
  · rw [min_eq_right hlt.le]
    by_contra hcon
    push_neg at hcon
    have h1 : p ^ (val p b + 1) ∣ (a + b) := (pow_dvd_iff_le_val hp hab).mpr hcon
    have h2 : p ^ (val p b + 1) ∣ a :=
      dvd_trans (pow_dvd_pow p hlt) (pow_val_dvd hp ha)
    have h3 : p ^ (val p b + 1) ∣ b := by
      have := Nat.dvd_sub h1 h2
      simpa using this
    exact absurd ((pow_dvd_iff_le_val hp hb).mp h3) (by omega)
