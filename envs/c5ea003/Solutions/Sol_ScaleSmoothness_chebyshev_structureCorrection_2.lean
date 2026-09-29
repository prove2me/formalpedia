-- Prove2me | solution 2 for ScaleSmoothness.chebyshev_structureCorrection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:53:39.405969+00:00
-- url     : https://prove2.me/submissions/fb2c268a-d21f-4219-8d87-bb88a429fc8f

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
-- NOTE: the mirror's `variable` line contributes a FIRST copy of `(a, Fact, hodd)` that the
-- API statement does not show, so the real target takes the triple twice (the second
-- shadows the first in the body). The leading triple is therefore unused here.
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a₀ : ι → ℕ)
    [∀ i, Fact (a₀ i).Prime] (hodd₀ : ∀ i, a₀ i ≠ 2) (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) {t : ℚ} (ht : 0 < t) :
    t ^ 2 * (#{N : (∀ i, ZMod (a i)) | t ≤ |structureCorrection a N - 1|} : ℚ) ≤
      (∏ i, (a i : ℚ)) * (dispersionBound a - 1) := by
  classical
  haveI hnz : ∀ i, NeZero (a i) := fun i => ⟨(Fact.out : (a i).Prime).ne_zero⟩
  -- ===== per-coordinate first moment (the `sum_localFactor` argument) =====
  have hLF : ∀ i : ι, ∑ x : ZMod (a i), localFactor (a i) x = ((a i : ℕ) : ℚ) := by
    intro i
    have hp : a i ≠ 2 := hodd i
    haveI : NeZero (a i) := ⟨(Fact.out : (a i).Prime).ne_zero⟩
    have hp2 : 2 ≤ (a i) := (Fact.out : (a i).Prime).two_le
    have hp3 : 3 ≤ (a i) := by omega
    -- the fibres of `x ↦ x²` partition `ZMod (a i)`, so the dial values sum to `(a i)`
    have hd : ∑ N : ZMod (a i), dial (a i) N = (a i) := by
      have h : (Finset.univ : Finset (ZMod (a i))).card
          = ∑ N ∈ (Finset.univ : Finset (ZMod (a i))),
            ((Finset.univ : Finset (ZMod (a i))).filter (fun x => x ^ 2 = N)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
      simp only [dial]
      rw [← h, Finset.card_univ, ZMod.card]
    have hcast : ∑ N : ZMod (a i), ((dial (a i) N : ℚ)) = ((a i) : ℚ) := by
      rw [← Nat.cast_sum, hd]
    have hne : (((a i) : ℚ) - 1) ≠ 0 := by
      have h3 : (3 : ℚ) ≤ ((a i) : ℚ) := by exact_mod_cast hp3
      intro h
      linarith
    simp only [localFactor]
    rw [← Finset.sum_div]
    have hsum : ∑ N : ZMod (a i), (((a i) : ℚ) - (dial (a i) N : ℚ)) = ((a i) : ℚ) * ((a i) : ℚ) - ((a i) : ℚ) := by
      rw [Finset.sum_sub_distrib, hcast, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [hsum]
    field_simp
  -- ===== per-coordinate second moment (the `sum_localFactor_sq` argument) =====
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
  -- ===== bounds on each `a i` =====
  have ha3 : ∀ i, 3 ≤ a i := by
    intro i
    have h2 : 2 ≤ a i := (Fact.out : (a i).Prime).two_le
    have := hodd i
    omega
  have hb0 : ∀ i, ((a i : ℕ) : ℚ) ≠ 0 := by
    intro i
    have : (3 : ℚ) ≤ ((a i : ℕ) : ℚ) := by exact_mod_cast ha3 i
    intro h; rw [h] at this; linarith
  have hb1 : ∀ i, ((a i : ℕ) : ℚ) - 1 ≠ 0 := by
    intro i
    have : (3 : ℚ) ≤ ((a i : ℕ) : ℚ) := by exact_mod_cast ha3 i
    intro h; linarith
  -- ===== Fubini over the product type =====
  have hfub : ∀ g : (∀ i, ZMod (a i) → ℚ),
      ∑ N : (∀ i, ZMod (a i)), ∏ i, g i (N i) = ∏ i, ∑ x : ZMod (a i), g i x := by
    intro g
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr (by simp) (fun _ _ => rfl)
  have hSC : ∑ N : (∀ i, ZMod (a i)), structureCorrection a N = ∏ i, ((a i : ℕ) : ℚ) := by
    simp only [structureCorrection]
    rw [hfub (fun i x => localFactor (a i) x)]
    exact Finset.prod_congr rfl fun i _ => hLF i
  have hSC2 : ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N) ^ 2
      = ∏ i, (((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1)) := by
    simp only [structureCorrection, ← Finset.prod_pow]
    rw [hfub (fun i x => (localFactor (a i) x) ^ 2)]
    exact Finset.prod_congr rfl fun i _ => hLF2 i
  have hcard : ((Fintype.card (∀ i, ZMod (a i)) : ℚ)) = ∏ i, ((a i : ℕ) : ℚ) := by
    rw [Fintype.card_pi]
    push_cast
    exact Finset.prod_congr rfl fun i _ => by rw [ZMod.card]
  -- ===== the second moment of `SC - 1` =====
  have hmom : ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2
      = (∏ i, (((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1))) - ∏ i, ((a i : ℕ) : ℚ) := by
    have hexp : ∀ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2
        = (structureCorrection a N) ^ 2 - 2 * structureCorrection a N + 1 := by
      intro N; ring
    rw [Finset.sum_congr rfl (fun N _ => hexp N), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hSC2, ← Finset.mul_sum, hSC, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcard]
    ring
  -- ===== the right-hand side is exactly that second moment =====
  have hrhs : (∏ i, ((a i : ℕ) : ℚ)) * (dispersionBound a - 1)
      = (∏ i, (((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1))) - ∏ i, ((a i : ℕ) : ℚ) := by
    have key : (∏ i, ((a i : ℕ) : ℚ)) * ∏ i, (1 + 1 / (((a i : ℕ) : ℚ) * (((a i : ℕ) : ℚ) - 1)))
        = ∏ i, (((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      have h1 := hb0 i
      have h2 := hb1 i
      field_simp
    simp only [dispersionBound]
    rw [mul_sub, mul_one, key]
  -- ===== Chebyshev =====
  have hcheb : t ^ 2 * (((Finset.univ.filter
        (fun N : (∀ i, ZMod (a i)) => t ≤ |structureCorrection a N - 1|)).card : ℚ))
      ≤ ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2 := by
    set S := Finset.univ.filter (fun N : (∀ i, ZMod (a i)) => t ≤ |structureCorrection a N - 1|)
      with hS
    have h1 : t ^ 2 * (S.card : ℚ) = ∑ _N ∈ S, t ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h2 : ∑ _N ∈ S, t ^ 2 ≤ ∑ N ∈ S, (structureCorrection a N - 1) ^ 2 := by
      refine Finset.sum_le_sum fun N hN => ?_
      have hab : t ≤ |structureCorrection a N - 1| := (Finset.mem_filter.mp hN).2
      nlinarith [abs_nonneg (structureCorrection a N - 1),
        sq_abs (structureCorrection a N - 1)]
    have h3 : ∑ N ∈ S, (structureCorrection a N - 1) ^ 2
        ≤ ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
    linarith
  rw [hrhs, ← hmom]
  exact hcheb
