-- Prove2me | solution 1 for KappaDial.card_valPeriod_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:46:22.871075+00:00
-- url     : https://prove2.me/submissions/589eead2-904a-4b68-af14-809a6acd9cf8

-- Sol generated from Combinatorics/KappaDialRefinement.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaDialRefinement
import Definitions.Def_Combinatorics_KappaRateDial
import Theorems.Thm_KappaDial_card_range_val_cell
import Theorems.Thm_KappaDial_count_mul_coprime
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

/-- Divisibility by a divisor of the modulus only depends on the residue. -/
lemma dvd_iff_dvd_of_mod_eq {a n v w : ℕ} (ha : a ∣ n) (h : v % n = w % n) :
    a ∣ v ↔ a ∣ w := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd v ha,
    ← Nat.mod_mod_of_dvd w ha, h]

/-! ## 1. Equidistribution across residue classes at any coprime scale -/




/-! ## 2. The valuation ladder: exact `p`-adic valuation cells -/




lemma valPeriod_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) :
    0 < valPeriod P e :=
  Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _


lemma inValCell_periodic (P : Finset ℕ) (e : ℕ → ℕ) {L : ℕ}
    (hL : ∀ p ∈ P, p ^ (e p + 1) ∣ L) (v w : ℕ) (h : v % L = w % L) :
    InValCell P e v ↔ InValCell P e w := by
  unfold InValCell
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hdL : p ^ (e p + 1) ∣ L := hL p hp
  have hdL' : p ^ (e p) ∣ L := dvd_trans (pow_dvd_pow p (Nat.le_succ _)) hdL
  rw [dvd_iff_dvd_of_mod_eq hdL' h, dvd_iff_dvd_of_mod_eq hdL h]




/-! ## 3. Effective size of a cell sweep -/








/-! ## Worked instances -/








open KappaDial in
theorem solution(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) :
    ((range (valPeriod P e)).filter (InValCell P e)).card = ∏ p ∈ P, (p - 1) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      have h : (range (valPeriod (∅ : Finset ℕ) e)).filter (InValCell ∅ e) = {0} := by
        simp only [valPeriod, Finset.prod_empty]
        rw [Finset.filter_true_of_mem (fun x _ => by intro p hp; simp at hp)]
        rfl
      rw [h]; simp
  | insert q P' hq ih =>
      have hqp : q.Prime := hP q (Finset.mem_insert_self q P')
      have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hper : valPeriod (insert q P') e = q ^ (e q + 1) * valPeriod P' e := by
        simp [valPeriod, Finset.prod_insert hq]
      have hcop : Nat.Coprime (q ^ (e q + 1)) (valPeriod P' e) := by
        refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => ?_)
        exact Nat.Coprime.pow_right _
          ((Nat.coprime_primes hqp (hP' p hp)).mpr (fun h => hq (h ▸ hp)))
      have hsplit : ∀ v, InValCell (insert q P') e v ↔
          ((q ^ (e q) ∣ v ∧ ¬ q ^ (e q + 1) ∣ v) ∧ InValCell P' e v) := by
        intro v; unfold InValCell; simp
      rw [hper, Finset.filter_congr (fun v _ => (hsplit v)),
        count_mul_coprime (q ^ (e q + 1)) (valPeriod P' e) (pow_pos hqp.pos _)
          (valPeriod_pos P' hP' e) hcop _ _
          (fun v w hvw => by
            have hqe : q ^ (e q) ∣ q ^ (e q + 1) := pow_dvd_pow q (Nat.le_succ _)
            rw [dvd_iff_dvd_of_mod_eq hqe hvw, dvd_iff_dvd_of_mod_eq dvd_rfl hvw])
          (fun v w hvw =>
            inValCell_periodic P' e (fun p hp => Finset.dvd_prod_of_mem _ hp) v w hvw),
        card_range_val_cell q (e q) hqp, ih hP', Finset.prod_insert hq]
