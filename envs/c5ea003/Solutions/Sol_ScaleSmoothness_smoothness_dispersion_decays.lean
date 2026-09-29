-- Prove2me | solution 1 for ScaleSmoothness.smoothness_dispersion_decays
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:56:35.291989+00:00
-- url     : https://prove2.me/submissions/8a0cf301-4f32-412f-a76a-6fa43f9521de

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
import Definitions.Def_NumberTheory_SmoothnessDispersionDecay
open ScaleSmoothness Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) (hinj : Function.Injective a) {K : Type*} [Fintype K]
    (P : (∀ i, ZMod (a i)) → K → ℚ) (val : K → ℚ) (lam q : ℚ)
    (hlam : 0 ≤ lam) (hq : 0 ≤ q)
    (hP : ∀ N, ∑ k, P N k = 1)
    (hmean : ∀ N, condMean P val N = lam * structureCorrection a N)
    (hvar : ∀ N, condVar P val N = lam * structureCorrection a N
      * (1 - q * structureCorrection a N)) :
    |mixVar (uniformWeight a) P val - mixMean (uniformWeight a) P val|
      ≤ lam * (lam + 2 * q) := by
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

  -- ===== the two uniform moments of the structure correction =====
  have hb0 : ∀ i, ((a i : ℕ) : ℚ) ≠ 0 := by
    intro i
    have : (3 : ℚ) ≤ ((a i : ℕ) : ℚ) := by exact_mod_cast ha3 i
    intro h; rw [h] at this; linarith
  have hprodpos : (0 : ℚ) < ∏ i, ((a i : ℕ) : ℚ) := by
    refine Finset.prod_pos fun i _ => ?_
    have : (3 : ℚ) ≤ ((a i : ℕ) : ℚ) := by exact_mod_cast ha3 i
    linarith
  have hESC : ∑ N : (∀ i, ZMod (a i)), uniformWeight a N * structureCorrection a N = 1 := by
    simp only [uniformWeight]
    rw [← Finset.mul_sum, hSC]
    field_simp
  have hESC2 : ∑ N : (∀ i, ZMod (a i)),
      uniformWeight a N * (structureCorrection a N) ^ 2 = dispersionBound a := by
    simp only [uniformWeight]
    rw [← Finset.mul_sum, hSC2, dispersionBound]
    have key : (∏ i, ((a i : ℕ) : ℚ))
        * ∏ i, (1 + 1 / (((a i : ℕ) : ℚ) * (((a i : ℕ) : ℚ) - 1)))
        = ∏ i, (((a i : ℕ) : ℚ) + 1 / (((a i : ℕ) : ℚ) - 1)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      have h1 := hb0 i
      have h2 := hb1 i
      field_simp
    rw [← key]
    field_simp
  -- ===== total weight is one =====
  have hw1 : ∑ N : (∀ i, ZMod (a i)), uniformWeight a N = 1 := by
    simp only [uniformWeight]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  -- ===== the dispersion bound `1 ≤ D ≤ 2` =====
  -- the telescoping bound `∑_{n ≥ 3} 1/(n(n-1)) ≤ 1/2` (the `sum_inv_le_half` argument)
  have hinv : ∀ S : Finset ℕ, (∀ n ∈ S, 3 ≤ n) →
      ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) ≤ 1 / 2 := by
    intro S hS
    -- partial fractions: `1/(n(n-1)) = 1/(n-1) - 1/n`, the source of the telescoping
    have hsplit : ∀ x : ℚ, x + 2 ≠ 0 → x + 3 ≠ 0 →
        1 / ((x + 3) * ((x + 3) - 1)) = 1 / (x + 2) - 1 / (x + 3) := by
      intro x h2 h3
      rw [show x + 3 - 1 = x + 2 by ring, div_sub_div _ _ h2 h3,
        show 1 * (x + 3) - (x + 2) * 1 = 1 by ring, mul_comm (x + 2) (x + 3)]
    -- the telescoping identity `∑_{n=3}^{m+2} 1/(n(n-1)) = 1/2 - 1/(m+2)`
    have key : ∀ m : ℕ, ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        = 1 / 2 - 1 / ((m : ℚ) + 2) := by
      intro m
      induction m with
      | zero =>
        rw [Finset.Icc_eq_empty (by omega)]
        norm_num
      | succ k ih =>
        have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
        have h3 : (k : ℚ) + 3 ≠ 0 := by positivity
        have hc : ((k + 2 + 1 : ℕ) : ℚ) = (k : ℚ) + 3 := by push_cast; ring
        have hc2 : ((k + 1 : ℕ) : ℚ) + 2 = (k : ℚ) + 3 := by push_cast; ring
        rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih,
          hc, hsplit (k : ℚ) h2 h3, hc2]
        ring
    -- every element of `S` lies in `Icc 3 (sup S + 2)`
    set m := S.sup id with hm
    have hsub : S ⊆ Finset.Icc 3 (m + 2) := by
      intro n hn
      simp only [Finset.mem_Icc]
      refine ⟨hS n hn, ?_⟩
      have := Finset.le_sup (f := id) hn
      simp only [id] at this
      omega
    have hnn : ∀ n ∈ Finset.Icc 3 (m + 2), n ∉ S → (0 : ℚ) ≤ 1 / ((n : ℚ) * ((n : ℚ) - 1)) := by
      intro n hn _
      simp only [Finset.mem_Icc] at hn
      have h3 : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn.1
      apply div_nonneg zero_le_one
      nlinarith
    calc ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        ≤ ∑ n ∈ Finset.Icc 3 (m + 2), (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
      _ = 1 / 2 - 1 / ((m : ℚ) + 2) := key m
      _ ≤ 1 / 2 := by
          have hpos : (0 : ℚ) < (m : ℚ) + 2 := by positivity
          have := one_div_pos.mpr hpos
          linarith
  -- transport it along the injective family `a`
  have hsum : ∑ i, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) ≤ 1 / 2 := by
    have himg : ∑ n ∈ Finset.univ.image a, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1))
        = ∑ i, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) :=
      Finset.sum_image (fun x _ y _ h => hinj h)
    rw [← himg]
    refine hinv _ ?_
    intro n hn
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
    exact ha3 i
  have hnn : ∀ i, (0 : ℚ) ≤ 1 / ((a i : ℚ) * ((a i : ℚ) - 1)) := by
    intro i
    have h3 : (3 : ℚ) ≤ (a i : ℚ) := by exact_mod_cast ha3 i
    apply div_nonneg zero_le_one
    nlinarith
  -- `∏ (1 + xᵢ) ≤ 1 + 2 ∑ xᵢ` whenever the partial sums stay below `1/2`
  have hprod : ∀ s : Finset ι, (∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 1 / 2 →
      ∏ i ∈ s, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)))
        ≤ 1 + 2 * ∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert j s hj ih =>
      intro hle
      rw [Finset.sum_insert hj] at hle
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      have hx := hnn j
      have hS : (∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 1 / 2 := by linarith
      have hSnn : (0 : ℚ) ≤ ∑ i ∈ s, (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)) :=
        Finset.sum_nonneg fun i _ => hnn i
      have hih := ih hS
      nlinarith [hih, hx, hS, hSnn]
  have hD2 : dispersionBound a ≤ 2 := by
    have hfin := hprod Finset.univ hsum
    show ∏ i, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) ≤ 2
    linarith
  have hD1 : (1 : ℚ) ≤ dispersionBound a := by
    show (1 : ℚ) ≤ ∏ i, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1)))
    calc (1 : ℚ) = ∏ _i : ι, (1 : ℚ) := by simp
      _ ≤ ∏ i, (1 + (1 : ℚ) / ((a i : ℚ) * ((a i : ℚ) - 1))) :=
          Finset.prod_le_prod (fun i _ => by norm_num)
            (fun i _ => by have := hnn i; linarith)
  -- ===== variance decomposition =====
  set M := mixMean (uniformWeight a) P val with hMdef
  have hz : ∀ N, ∑ k, P N k * (val k - condMean P val N) = 0 := by
    intro N
    have e : ∀ k, P N k * (val k - condMean P val N)
        = P N k * val k - condMean P val N * P N k := by intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib, ← Finset.mul_sum, hP N,
      mul_one]
    simp [condMean]
  have hdecomp : ∀ N, ∑ k, P N k * (val k - M) ^ 2
      = condVar P val N + (condMean P val N - M) ^ 2 := by
    intro N
    have e2 : ∀ k, P N k * (val k - M) ^ 2
        = P N k * (val k - condMean P val N) ^ 2
          + (2 * (condMean P val N - M)) * (P N k * (val k - condMean P val N))
          + (condMean P val N - M) ^ 2 * P N k := by intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hz N, mul_zero, add_zero, ← Finset.mul_sum, hP N, mul_one]
    rfl
  -- ===== evaluate both sides =====
  have hMval : M = lam := by
    rw [hMdef]
    simp only [mixMean]
    have e : ∀ N : (∀ i, ZMod (a i)), uniformWeight a N * condMean P val N
        = lam * (uniformWeight a N * structureCorrection a N) := by
      intro N; rw [hmean N]; ring
    rw [Finset.sum_congr rfl (fun N _ => e N), ← Finset.mul_sum, hESC, mul_one]
  -- ===== evaluate the mixture variance =====
  have hmixvar : mixVar (uniformWeight a) P val
      = (lam - lam * q * dispersionBound a) + lam ^ 2 * (dispersionBound a - 1) := by
    simp only [mixVar]
    have e : ∀ N : (∀ i, ZMod (a i)), uniformWeight a N * ∑ k, P N k * (val k - M) ^ 2
        = lam * (uniformWeight a N * structureCorrection a N)
          - lam * q * (uniformWeight a N * (structureCorrection a N) ^ 2)
          + lam ^ 2 * (uniformWeight a N * (structureCorrection a N) ^ 2)
          - 2 * lam ^ 2 * (uniformWeight a N * structureCorrection a N)
          + lam ^ 2 * uniformWeight a N := by
      intro N
      rw [hdecomp N, hvar N, hmean N, hMval]
      ring
    rw [Finset.sum_congr rfl (fun N _ => e N)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hESC, hESC2, hw1]
    ring
  -- ===== the bound =====
  rw [hmixvar, hMval, abs_le]
  constructor <;> nlinarith [hD1, hD2, hlam, hq, mul_nonneg hlam hq,
    mul_nonneg (mul_nonneg hlam hq) (le_trans zero_le_one hD1)]
