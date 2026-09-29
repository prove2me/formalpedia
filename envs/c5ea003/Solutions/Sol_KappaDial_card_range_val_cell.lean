-- Prove2me | solution 1 for KappaDial.card_range_val_cell
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:44:58.214004+00:00
-- url     : https://prove2.me/submissions/35180126-e343-47aa-b5ab-c99b6c69564b

-- Sol generated from Combinatorics/KappaDialRefinement.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaDialRefinement
import Definitions.Def_Combinatorics_KappaRateDial
/-
# Refinements of the κ rate–dial: coprime-scale equidistribution, the valuation ladder,
# and the effective size of a cell sweep

Building on `Combinatorics.KappaRateDial`, this file pushes the "rate dial, not a position
dial" dichotomy in three directions.

1. **A coprime-statistic no-go theorem** (`cellCount_coprime_statistic`, and its
   equidistribution corollary `cellCount_coprime_residue`). The absence of a positional
   signal is not merely a statement about whole period blocks: for *any* modulus `M` coprime
   to the period `L` and *any* statistic `Q` depending only on `v mod M`, the divisibility
   cell and the event `Q` are *exactly independent* over one common period. In particular
   each residue class mod `M` receives exactly `κ(σ)` members of the cell inside `[0, L·M)`.
   A divisibility cell therefore carries *no* information about any coprime-measurable
   observable, uniformly.

2. **The valuation ladder** (`card_valPeriod_eq`). Refining "`p ∣ v`" to "`v_p(v) = e p`"
   produces, over the refined period `∏ p^{e p + 1}`, a cell of size *exactly* `∏ (p - 1)`,
   **independently of the exponents** `e`. Sharpening the resolution of the dial therefore
   changes only the period (the denominator), never the numerator: the rate dial is a pure
   geometric ladder `∏ p^{-e p} (1 - 1/p)`.

3. **Effective sweep size** (`sweep_image_card_le`, `sweepValues_card_eq_iff`). Because the
   prime `2` is a dead coordinate, a sweep over all `2^{|P|}` divisibility cells explores at
   most `2^{|P| - 1}` distinct rate values when `2 ∈ P`; and it attains that maximum exactly
   when the numbers `p - 1` over the odd primes of `P` have pairwise distinct subset
   products. Quantifying the effective number of degrees of freedom of a cell sweep is
   exactly what a max-statistic selection correction needs. The criterion is not vacuous:
   `sweep_collision_3_7_13` exhibits a prime set where it fails.

## Lab notes

`P = {2,3,5,7}`, `L = 210`, all-cleared cell, `M = 11`: each of the 11 residue classes mod
`11` inside `[0, 2310)` contains exactly `48` totatives of `210` — checked by the general
theorem and instantiated in `cellCount_coprime_residue_example`.

Valuation ladder for `p = 3`, `e = 0,1,2`: cells of size `2` inside periods `3, 9, 27`, i.e.
densities `2/3, 2/9, 2/27` — a clean geometric ladder with constant numerator.
-/


open Finset

open KappaDial


/-! ## 1. Equidistribution across residue classes at any coprime scale -/




/-! ## 2. The valuation ladder: exact `p`-adic valuation cells -/










/-! ## 3. Effective size of a cell sweep -/








/-! ## Worked instances -/








open KappaDial in
theorem solution(p e : ℕ) (hp : p.Prime) :
    ((range (p ^ (e + 1))).filter (fun v => p ^ e ∣ v ∧ ¬ p ^ (e + 1) ∣ v)).card = p - 1 := by
  have hp0 : 0 < p := hp.pos
  have hpe : 0 < p ^ e := pow_pos hp0 e
  have hcard : ((range p).erase 0).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hp0), Finset.card_range]
  rw [← hcard]
  refine Finset.card_nbij (fun v => v / p ^ e) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hv ⊢
    obtain ⟨hv1, hdvd, hndvd⟩ := hv
    constructor
    · intro h0
      have : v = 0 := by
        obtain ⟨k, rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left _ hpe] at h0
        simp [h0]
      exact hndvd (this ▸ dvd_zero _)
    · rw [Nat.div_lt_iff_lt_mul hpe, mul_comm]
      calc v < p ^ (e + 1) := hv1
        _ = p ^ e * p := pow_succ p e
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv hw
    obtain ⟨k, rfl⟩ := hv.2.1
    obtain ⟨l, rfl⟩ := hw.2.1
    dsimp only at hvw
    rw [Nat.mul_div_cancel_left _ hpe, Nat.mul_div_cancel_left _ hpe] at hvw
    rw [hvw]
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_range] at hk
    obtain ⟨hk0, hkp⟩ := hk
    refine ⟨p ^ e * k, ?_, Nat.mul_div_cancel_left _ hpe⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Dvd.intro k rfl, ?_⟩
    · calc p ^ e * k < p ^ e * p := by exact mul_lt_mul_of_pos_left hkp hpe
        _ = p ^ (e + 1) := (pow_succ p e).symm
    · rintro ⟨c, hc⟩
      have : k = p * c := by
        have hpe1 : p ^ (e + 1) = p ^ e * p := by ring
        rw [hpe1, mul_assoc] at hc
        exact Nat.eq_of_mul_eq_mul_left hpe hc
      have hpk : p ∣ k := ⟨c, this⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpk
      omega
