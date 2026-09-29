-- Prove2me | solution 2 for ScaleSmoothness.sum_structureCorrection_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:58:36.921108+00:00
-- url     : https://prove2.me/submissions/bce3ee50-3a7a-474e-9f78-2dbe66cb3559

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) :
    ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N) ^ 2 =
      ∏ i, ((a i : ℚ) + 1 / ((a i : ℚ) - 1)) := by
  classical
  haveI hnz : ∀ i, NeZero (a i) := fun i => ⟨(Fact.out : (a i).Prime).ne_zero⟩
  -- per-coordinate second moment (the `sum_localFactor_sq` argument)
  have hLF2 : ∀ i : ι, ∑ x : ZMod (a i), (localFactor (a i) x) ^ 2
      = ((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1) := by
    intro i
    have hp : a i ≠ 2 := hodd i
    haveI : NeZero (a i) := ⟨(Fact.out : (a i).Prime).ne_zero⟩
    have hp2 : 2 ≤ (a i) := (Fact.out : (a i).Prime).two_le
    have hp3 : 3 ≤ (a i) := by omega
    have hne : (((a i) : ℚ) - 1) ≠ 0 := by
      have h3 : (3 : ℚ) ≤ ((a i) : ℚ) := by exact_mod_cast hp3
      intro h
      linarith
    -- `2` is invertible in `ZMod (a i)` because `(a i)` is an odd prime
    have h2ne : (2 : ZMod (a i)) ≠ 0 := by
      have : ((2 : ℕ) : ZMod (a i)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      simpa using this
    -- the dial values sum to `(a i)` (the fibres of `x ↦ x²` partition `ZMod (a i)`)
    have hd : ∑ N : ZMod (a i), dial (a i) N = (a i) := by
      have h : (Finset.univ : Finset (ZMod (a i))).card
          = ∑ N ∈ (Finset.univ : Finset (ZMod (a i))),
            ((Finset.univ : Finset (ZMod (a i))).filter (fun x => x ^ 2 = N)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
      simp only [dial]
      rw [← h, Finset.card_univ, ZMod.card]
    have hcast : ∑ N : ZMod (a i), ((dial (a i) N : ℚ)) = ((a i) : ℚ) := by
      rw [← Nat.cast_sum, hd]
    -- `dial (a i) 0 = 1`: only `0` squares to `0` in a field
    have hd0 : dial (a i) 0 = 1 := by
      show ((Finset.univ : Finset (ZMod (a i))).filter (fun x => x ^ 2 = 0)).card = 1
      have : ((Finset.univ : Finset (ZMod (a i))).filter (fun x => x ^ 2 = 0)) = {0} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hy
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
        · intro hy
          rw [hy]
          ring
      rw [this, Finset.card_singleton]
    -- for `N ≠ 0` the fibre is either empty or the two-element set `{x, -x}`
    have hfib : ∀ N : ZMod (a i), N ≠ 0 → dial (a i) N = 0 ∨ dial (a i) N = 2 := by
      intro N hN
      by_cases hex : ∃ x : ZMod (a i), x ^ 2 = N
      · obtain ⟨x, hx⟩ := hex
        right
        have hx0 : x ≠ 0 := by
          intro h
          rw [h] at hx
          exact hN (by rw [← hx]; ring)
        have hxne : x ≠ -x := by
          intro h
          have h2x : (2 : ZMod (a i)) * x = 0 := by linear_combination h
          rcases mul_eq_zero.mp h2x with h' | h'
          · exact h2ne h'
          · exact hx0 h'
        show ((Finset.univ : Finset (ZMod (a i))).filter (fun y => y ^ 2 = N)).card = 2
        have hset : ((Finset.univ : Finset (ZMod (a i))).filter (fun y => y ^ 2 = N)) = {x, -x} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · intro hy
            have hfac : (y - x) * (y + x) = 0 := by linear_combination hy - hx
            rcases mul_eq_zero.mp hfac with h' | h'
            · exact Or.inl (by linear_combination h')
            · exact Or.inr (by linear_combination h')
          · rintro (rfl | rfl)
            · exact hx
            · rw [← hx]; ring
        rw [hset, Finset.card_insert_of_notMem (by simpa using hxne), Finset.card_singleton]
      · left
        show ((Finset.univ : Finset (ZMod (a i))).filter (fun y => y ^ 2 = N)).card = 0
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y _
        exact fun h => hex ⟨y, h⟩
    -- hence `∑ dial² = 2p - 1`
    have hsplit : ∀ N : ZMod (a i),
        ((dial (a i) N : ℚ)) ^ 2 = 2 * (dial (a i) N : ℚ) - (if N = 0 then (1 : ℚ) else 0) := by
      intro N
      by_cases hN : N = 0
      · subst hN
        rw [hd0]
        norm_num
      · rcases hfib N hN with h | h <;> rw [h] <;> norm_num [hN]
    have hd2 : ∑ N : ZMod (a i), ((dial (a i) N : ℚ)) ^ 2 = 2 * ((a i) : ℚ) - 1 := by
      rw [Finset.sum_congr rfl (fun N _ => hsplit N), Finset.sum_sub_distrib, ← Finset.mul_sum,
        hcast, Finset.sum_ite_eq' (Finset.univ : Finset (ZMod (a i))) (0 : ZMod (a i)) (fun _ => (1 : ℚ))]
      simp
    -- assemble
    simp only [localFactor, div_pow]
    rw [← Finset.sum_div]
    have hnum : ∑ N : ZMod (a i), (((a i) : ℚ) - (dial (a i) N : ℚ)) ^ 2
        = ((a i) : ℚ) ^ 3 - 2 * ((a i) : ℚ) ^ 2 + (2 * ((a i) : ℚ) - 1) := by
      have hexp : ∀ N : ZMod (a i), (((a i) : ℚ) - (dial (a i) N : ℚ)) ^ 2
          = ((a i) : ℚ) ^ 2 - 2 * ((a i) : ℚ) * (dial (a i) N : ℚ) + ((dial (a i) N : ℚ)) ^ 2 := by
        intro N; ring
      rw [Finset.sum_congr rfl (fun N _ => hexp N)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul, ← Finset.mul_sum, hcast, hd2]
      ring
    rw [hnum]
    field_simp
    ring
  -- Fubini: a sum over the product type of a product of coordinate functions
  have hfub : ∀ g : (∀ i, ZMod (a i) → ℚ),
      ∑ N : (∀ i, ZMod (a i)), ∏ i, g i (N i) = ∏ i, ∑ x : ZMod (a i), g i x := by
    intro g
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr (by simp) (fun _ _ => rfl)
  simp only [structureCorrection, ← Finset.prod_pow]
  rw [hfub (fun i x => (localFactor (a i) x) ^ 2)]
  exact Finset.prod_congr rfl fun i _ => hLF2 i
