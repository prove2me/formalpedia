-- Prove2me | solution 2 for ScaleSmoothness.card_dial_pattern
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:40:39.583811+00:00
-- url     : https://prove2.me/submissions/64c203b3-120b-4547-b070-fe8906d05909

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) (d : ι → ℕ) (hd : ∀ i, d i = 0 ∨ d i = 2) :
    2 ^ (Fintype.card ι) * #{N : (∀ i, ZMod (a i)) | ∀ i, dial (a i) (N i) = d i}
      = ∏ i, (a i - 1) := by
  classical
  haveI hnz : ∀ i, NeZero (a i) := fun i => ⟨(Fact.out : (a i).Prime).ne_zero⟩
  -- ===== per-coordinate counting =====
  have hcount : ∀ i : ι,
      2 * ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = d i)).card) = a i - 1 := by
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
    have hdsum : ∑ N : ZMod (a i), dial (a i) N = (a i) := by
      have h : (Finset.univ : Finset (ZMod (a i))).card
          = ∑ N ∈ (Finset.univ : Finset (ZMod (a i))),
            ((Finset.univ : Finset (ZMod (a i))).filter (fun x => x ^ 2 = N)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
      simp only [dial]
      rw [← h, Finset.card_univ, ZMod.card]
    have hcast : ∑ N : ZMod (a i), ((dial (a i) N : ℚ)) = ((a i) : ℚ) := by
      rw [← Nat.cast_sum, hdsum]
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
    -- the dial takes the value `2` on exactly half of the nonzero residues
    have hsumeq : ∑ x : ZMod (a i), dial (a i) x
        = 2 * ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 2)).card) + 1 := by
      have hpt : ∀ x : ZMod (a i), dial (a i) x
          = (if dial (a i) x = 2 then 2 else if x = 0 then 1 else 0) := by
        intro x
        by_cases hx2 : dial (a i) x = 2
        · simp [hx2]
        · by_cases hx0 : x = 0
          · subst hx0; simp [hd0, hx2]
          · rcases hfib x hx0 with h | h
            · simp [h, hx2, hx0]
            · exact absurd h hx2
      rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite, Finset.sum_const,
        smul_eq_mul, Finset.sum_ite_eq' (Finset.univ.filter
          (fun x : ZMod (a i) => ¬ (dial (a i) x = 2))) (0 : ZMod (a i)) (fun _ => 1)]
      have h0mem : (0 : ZMod (a i)) ∈ Finset.univ.filter
          (fun x : ZMod (a i) => ¬ (dial (a i) x = 2)) := by
        simp [hd0]
      rw [if_pos h0mem]
      ring
    have hq2 : 2 * ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 2)).card) + 1
        = a i := by rw [← hsumeq, hdsum]
    -- the complement of the `2`-fibre is `{0}` together with the `0`-fibre
    have hne2 : (Finset.univ.filter (fun x : ZMod (a i) => ¬ (dial (a i) x = 2)))
        = insert 0 (Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · rcases hfib x hx0 with h | h
          · exact Or.inr h
          · exact absurd h hx
      · rintro (rfl | h)
        · rw [hd0]; norm_num
        · rw [h]; norm_num
    have h0notin : (0 : ZMod (a i)) ∉
        Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 0) := by
      simp [hd0]
    have hpart : ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 2)).card)
        + (((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = 0)).card) + 1)
        = a i := by
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (ZMod (a i)))) (fun x => dial (a i) x = 2)
      rw [hne2, Finset.card_insert_of_notMem h0notin, Finset.card_univ, ZMod.card] at hsplit
      omega
    rcases hd i with hdi | hdi <;> rw [hdi] <;> omega
  -- ===== the pattern set is a product of coordinate fibres =====
  have hpi : (Finset.univ.filter (fun N : (∀ i, ZMod (a i)) => ∀ i, dial (a i) (N i) = d i))
      = Fintype.piFinset (fun i => Finset.univ.filter
          (fun x : ZMod (a i) => dial (a i) x = d i)) := by
    ext N
    simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  -- ===== assemble: `2^|ι| · ∏ cᵢ = ∏ (2·cᵢ) = ∏ (aᵢ - 1)` =====
  calc 2 ^ (Fintype.card ι)
        * ∏ i, ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = d i)).card)
      = ∏ i, (2 * ((Finset.univ.filter (fun x : ZMod (a i) => dial (a i) x = d i)).card)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = ∏ i, (a i - 1) := Finset.prod_congr rfl fun i _ => hcount i
