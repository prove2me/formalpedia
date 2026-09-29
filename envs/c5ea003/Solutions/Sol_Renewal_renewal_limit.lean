-- Prove2me | solution 1 for Renewal.renewal_limit
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T18:28:01.576455+00:00
-- url     : https://prove2.me/submissions/bd550d9b-41ee-47db-b313-e665390437fc

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.NumberTheory.FrobeniusNumber

set_option maxHeartbeats 1000000

open Filter Finset
open scoped Topology

/-- **Erdős–Feller–Pollard renewal theorem** (aperiodic, finite-mean case). -/
theorem solution (f r u : ℕ → ℝ) (mu : ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hstep : ∀ n : ℕ, r n = r (n + 1) + f (n + 1))
    (hr0 : r 0 = 1)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (hmean : HasSum r mu)
    (hape : ∀ d : ℕ, 2 ≤ d → ∃ k : ℕ, 0 < f k ∧ ¬ (d ∣ k))
    (hu0 : u 0 = 1)
    (hurec : ∀ n : ℕ, u (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k)) :
    Filter.Tendsto u Filter.atTop (nhds (1 / mu)) := by
  classical
  -- `r` is antitone and nonnegative
  have hanti : ∀ n, r (n + 1) ≤ r n := by
    intro n; rw [hstep n]; linarith [hf (n + 1)]
  have hantitone : Antitone r := antitone_nat_of_succ_le hanti
  have hrnn : ∀ n, 0 ≤ r n := by
    intro n
    refine le_of_tendsto hrlim ?_
    filter_upwards [eventually_ge_atTop n] with m hm using hantitone hm
  -- partial sums of `f`
  have hpart : ∀ n, ∑ k ∈ Finset.range n, f (k + 1) = 1 - r n := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, hr0]; ring
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, hstep n]
        ring
  have hfsum_le : ∀ n, ∑ k ∈ Finset.range n, f (k + 1) ≤ 1 := by
    intro n; rw [hpart n]; linarith [hrnn n]
  -- `u` takes values in `[0,1]`
  have hu01 : ∀ n, 0 ≤ u n ∧ u n ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        match n with
        | 0 => rw [hu0]; norm_num
        | (m + 1) =>
            rw [hurec m]
            constructor
            · refine Finset.sum_nonneg (fun k hk => ?_)
              exact mul_nonneg (hf _) (ih (m - k) (by
                rw [Finset.mem_range] at hk; omega)).1
            · calc ∑ k ∈ Finset.range (m + 1), f (k + 1) * u (m - k)
                  ≤ ∑ k ∈ Finset.range (m + 1), f (k + 1) * 1 := by
                    refine Finset.sum_le_sum (fun k hk => ?_)
                    rw [Finset.mem_range] at hk
                    exact mul_le_mul_of_nonneg_left (ih (m - k) (by omega)).2 (hf _)
                _ = ∑ k ∈ Finset.range (m + 1), f (k + 1) := by
                    simp
                _ ≤ 1 := hfsum_le _
  have hunn : ∀ n, 0 ≤ u n := fun n => (hu01 n).1
  have hule : ∀ n, u n ≤ 1 := fun n => (hu01 n).2
  -- the renewal identity `∑_{j ≤ n} u j * r (n - j) = 1`
  have hid : ∀ n, ∑ j ∈ Finset.range (n + 1), u j * r (n - j) = 1 := by
    intro n
    induction n with
    | zero => simp [hu0, hr0]
    | succ n ih =>
        have hsplit : ∑ j ∈ Finset.range (n + 2), u j * r (n + 1 - j)
            = (∑ j ∈ Finset.range (n + 1), u j * r (n + 1 - j)) + u (n + 1) * r 0 := by
          rw [Finset.sum_range_succ, Nat.sub_self]
        have hterm : ∀ j ∈ Finset.range (n + 1),
            u j * r (n + 1 - j) = u j * r (n - j) - u j * f (n + 1 - j) := by
          intro j hj
          rw [Finset.mem_range] at hj
          have h1 : n - j = (n + 1 - j - 1) := by omega
          have h2 : n + 1 - j = (n - j) + 1 := by omega
          rw [h2, hstep (n - j)]
          have h3 : n - j + 1 = n + 1 - j := by omega
          rw [h3]
          ring
        have hreflect : ∑ j ∈ Finset.range (n + 1), u j * f (n + 1 - j)
            = ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have h1 : n + 1 - (n + 1 - 1 - k) = k + 1 := by omega
          have h2 : n + 1 - 1 - k = n - k := by omega
          rw [h1, h2]
          ring
        rw [hsplit, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ih, hreflect,
          ← hurec n, hr0]
        ring
  have hid2 : ∀ n, ∑ j ∈ Finset.range (n + 1), u (n - j) * r j = 1 := by
    intro n
    rw [← hid n, ← Finset.sum_range_reflect (fun j => u j * r (n - j)) (n + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have e1 : n + 1 - 1 - j = n - j := by omega
    have e2 : n - (n - j) = j := by omega
    rw [e1, e2]
  -- the mean is at least one
  have hmu1 : (1:ℝ) ≤ mu := by
    have h := le_hasSum hmean 0 (fun i _ => hrnn i)
    rwa [hr0] at h
  have hmupos : (0:ℝ) < mu := by linarith
  have hpartle : ∀ N : ℕ, ∑ j ∈ Finset.range N, r j ≤ mu :=
    fun N => sum_le_hasSum _ (fun i _ => hrnn i) hmean
  have htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, mu - ∑ j ∈ Finset.range N, r j < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmean.tendsto_sum_nat ε hε
    refine ⟨N, ?_⟩
    have h1 := hN N (le_refl N)
    rw [Real.dist_eq] at h1
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  -- the support of the waiting-time law
  set Sset : Set ℕ := {k | 0 < f k ∧ 1 ≤ k} with hSset
  have hSmem : ∀ k, 0 < f k → 1 ≤ k → k ∈ Sset := fun k h1 h2 => ⟨h1, h2⟩
  have hexS : ∃ k, k ∈ Sset := by
    by_contra hc
    push_neg at hc
    have hz : ∀ k : ℕ, f (k + 1) = 0 := by
      intro k
      by_contra hne
      have hpos : 0 < f (k + 1) := lt_of_le_of_ne (hf _) (Ne.symm hne)
      exact hc (k + 1) (hSmem (k + 1) hpos (by omega))
    have hr1 : ∀ n, r n = 1 := by
      intro n
      have h2 := hpart n
      rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range n) => hz k),
        Finset.sum_const_zero] at h2
      linarith
    have hfun : r = fun _ => (1:ℝ) := funext hr1
    rw [hfun] at hrlim
    have := tendsto_nhds_unique hrlim tendsto_const_nhds
    norm_num at this
  -- the gcd of the support is one, so all large integers lie in its span
  have hgcd : Nat.setGcd Sset = 1 := by
    rcases Nat.eq_zero_or_pos (Nat.setGcd Sset) with h0 | hpos
    · exfalso
      obtain ⟨k, hk⟩ := hexS
      have hsub := Nat.setGcd_eq_zero_iff.mp h0
      have hk0 : k ∈ ({0} : Set ℕ) := hsub hk
      rw [Set.mem_singleton_iff] at hk0
      have hk1 : 1 ≤ k := hk.2
      omega
    · by_contra hne
      have h2 : 2 ≤ Nat.setGcd Sset := by omega
      obtain ⟨k, hk1, hk2⟩ := hape _ h2
      have hk0 : k ≠ 0 := by
        intro h; rw [h] at hk2; exact hk2 (dvd_zero _)
      exact hk2 (Nat.setGcd_dvd_of_mem (hSmem k hk1 (by omega)))
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ m : ℕ, J ≤ m → m ∈ AddSubmonoid.closure Sset := by
    obtain ⟨J, hJ⟩ := Nat.exists_mem_closure_of_ge Sset
    exact ⟨J, fun m hm => hJ m hm (by rw [hgcd]; exact one_dvd m)⟩
  -- limsup setup
  set L := Filter.limsup u Filter.atTop with hLdef
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n using hule n
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u := by
    refine ⟨0, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact le_trans (hunn n) hn
  have hL0 : 0 ≤ L :=
    Filter.le_limsup_of_frequently_le
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hunn)) hbdd
  -- one descent step, for any step size in the support
  have honestep : ∀ a : ℕ, 0 < f a → 1 ≤ a → ∀ ε : ℝ, 0 < ε →
      ∃ Nq : ℕ, ∀ m : ℕ, Nq ≤ m → ∀ b : ℝ, L - b ≤ u m →
        L - (b + 2 * ε) / f a ≤ u (m - a) := by
    intro a hfa ha1 ε hε
    have hfa1 : f a ≤ 1 := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      have h1 : f (c + 1) ≤ ∑ k ∈ Finset.range (c + 1), f (k + 1) :=
        Finset.single_le_sum (f := fun k => f (k + 1)) (fun k _ => hf _)
          (Finset.self_mem_range_succ c)
      exact h1.trans (hfsum_le (c + 1))
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (Filter.eventually_lt_of_limsup_lt (show L < L + ε by linarith) hbdd)
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
      (Filter.Tendsto.eventually_lt_const hε hrlim)
    refine ⟨N0 + N2 + a, fun m hm b hb => ?_⟩
    have hm1 : m - 1 + 1 = m := by omega
    have hurm : u m = ∑ k ∈ Finset.range m, f (k + 1) * u (m - 1 - k) := by
      have h := hurec (m - 1)
      rw [hm1] at h
      exact h
    have hsplit : ∑ k ∈ Finset.range m, f (k + 1) * u (m - 1 - k)
        = (∑ k ∈ Finset.range (m - N0), f (k + 1) * u (m - 1 - k))
          + ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) * u (m - 1 - k) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le (m - N0)) (by omega)]
    -- tail part
    have htail : ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) * u (m - 1 - k) ≤ ε := by
      have h1 : ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) * u (m - 1 - k)
          ≤ ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        calc f (k + 1) * u (m - 1 - k) ≤ f (k + 1) * 1 :=
              mul_le_mul_of_nonneg_left (hule _) (hf _)
          _ = f (k + 1) := by ring
      have h2 : ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1)
          = (∑ k ∈ Finset.range m, f (k + 1))
            - ∑ k ∈ Finset.range (m - N0), f (k + 1) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive (fun k => f (k + 1))
            (Nat.zero_le (m - N0)) (show m - N0 ≤ m by omega)]
        ring
      rw [h2, hpart, hpart] at h1
      have h3 : r (m - N0) < ε := hN2 (m - N0) (by omega)
      linarith [hrnn m]
    -- main part
    have hAmem : a - 1 ∈ Finset.range (m - N0) := by
      rw [Finset.mem_range]; omega
    have hAeq : f (a - 1 + 1) * u (m - 1 - (a - 1)) = f a * u (m - a) := by
      have e1 : a - 1 + 1 = a := by omega
      have e2 : m - 1 - (a - 1) = m - a := by omega
      rw [e1, e2]
    have hmain0 : ∑ k ∈ Finset.range (m - N0), f (k + 1) * u (m - 1 - k)
        ≤ f a * u (m - a) + (L + ε) * (1 - f a) := by
      rw [← Finset.add_sum_erase (Finset.range (m - N0))
        (fun k => f (k + 1) * u (m - 1 - k)) hAmem, hAeq]
      have hrest : ∑ k ∈ (Finset.range (m - N0)).erase (a - 1),
            f (k + 1) * u (m - 1 - k)
          ≤ (L + ε) * (1 - f a) := by
        have h1 : ∑ k ∈ (Finset.range (m - N0)).erase (a - 1),
              f (k + 1) * u (m - 1 - k)
            ≤ ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1) * (L + ε) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_erase, Finset.mem_range] at hk
          refine mul_le_mul_of_nonneg_left (le_of_lt (hN0 (m - 1 - k) ?_)) (hf _)
          omega
        have h2 : ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1)
            ≤ 1 - f a := by
          have h3 : f (a - 1 + 1)
              + ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1)
              = ∑ k ∈ Finset.range (m - N0), f (k + 1) :=
            Finset.add_sum_erase (Finset.range (m - N0)) (fun k => f (k + 1)) hAmem
          have e1 : a - 1 + 1 = a := by omega
          rw [e1, hpart] at h3
          linarith [hrnn (m - N0)]
        calc ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1) * u (m - 1 - k)
            ≤ ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1) * (L + ε) := h1
          _ = (∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1)) * (L + ε) := by
              rw [Finset.sum_mul]
          _ ≤ (1 - f a) * (L + ε) := by
              refine mul_le_mul_of_nonneg_right h2 (by linarith)
          _ = (L + ε) * (1 - f a) := by ring
      linarith
    have hfinal : L - b ≤ f a * u (m - a) + (L + ε) * (1 - f a) + ε := by
      rw [hurm, hsplit] at hb
      linarith
    have hstar : (L - u (m - a)) * f a ≤ b + 2 * ε := by nlinarith [hfinal, hfa, hε]
    have h2 : L - u (m - a) ≤ (b + 2 * ε) / f a := (le_div_iff₀ hfa).mpr hstar
    linarith

  -- descent by any element of the additive span of the support
  have hQ : ∀ m : ℕ, m ∈ AddSubmonoid.closure Sset →
      ∃ α β : ℝ, 0 < α ∧ 0 ≤ β ∧ ∀ ε : ℝ, 0 < ε → ∃ Nq : ℕ, ∀ n : ℕ, Nq ≤ n →
        ∀ b : ℝ, L - b ≤ u n → L - (α * b + β * ε) ≤ u (n - m) := by
    intro m hm
    refine AddSubmonoid.closure_induction ?_ ?_ ?_ hm
    · intro x hx
      obtain ⟨hfx, hx1⟩ := hx
      refine ⟨(f x)⁻¹, 2 * (f x)⁻¹, by positivity, by positivity, fun ε hε => ?_⟩
      obtain ⟨Nq, hNq⟩ := honestep x hfx hx1 ε hε
      refine ⟨Nq, fun n hn b hb => ?_⟩
      have h := hNq n hn b hb
      have hrw : (b + 2 * ε) / f x = (f x)⁻¹ * b + 2 * (f x)⁻¹ * ε := by
        field_simp
        try ring
      rwa [hrw] at h
    · refine ⟨1, 0, one_pos, le_refl 0, fun ε hε => ⟨0, fun n _ b hb => ?_⟩⟩
      rw [Nat.sub_zero]
      linarith
    · rintro x y - - ⟨α₁, β₁, hα₁, hβ₁, hx⟩ ⟨α₂, β₂, hα₂, hβ₂, hy⟩
      refine ⟨α₂ * α₁, α₂ * β₁ + β₂, by positivity, by positivity, fun ε hε => ?_⟩
      obtain ⟨Nq₁, hNq₁⟩ := hx ε hε
      obtain ⟨Nq₂, hNq₂⟩ := hy ε hε
      refine ⟨max Nq₁ (Nq₂ + x), fun n hn b hb => ?_⟩
      have hn1 : Nq₁ ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : Nq₂ ≤ n - x := by
        have := le_trans (le_max_right _ _) hn
        omega
      have h1 := hNq₁ n hn1 b hb
      have h2 := hNq₂ (n - x) hn2 (α₁ * b + β₁ * ε) h1
      have hsub : n - x - y = n - (x + y) := by omega
      rw [hsub] at h2
      calc L - (α₂ * α₁ * b + (α₂ * β₁ + β₂) * ε)
          = L - (α₂ * (α₁ * b + β₁ * ε) + β₂ * ε) := by ring
        _ ≤ u (n - (x + y)) := h2
  choose! alp bet halp hbet hQ' using hQ
  choose! Nq hNq using hQ'
  have hL1 : L ≤ 1 :=
    Filter.limsup_le_of_le hcobdd (Filter.Eventually.of_forall hule)
  -- the key upper bound on the limsup
  have hLkey : ∀ N : ℕ, L * (∑ j ∈ Finset.range (N + 1), r j) ≤ 1 := by
    intro N
    have hsumN : (0:ℝ) ≤ ∑ j ∈ Finset.range (N + 1), r j :=
      Finset.sum_nonneg (fun j _ => hrnn j)
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    -- choose the truncation level `M` for the law `f`
    obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ((J:ℝ) + 1) * mu < η / 2 := by
      refine ⟨(η / 2) / (2 * ((J:ℝ) + 1) * mu), by positivity, ?_⟩
      have heq : (η / 2) / (2 * ((J:ℝ) + 1) * mu) * ((J:ℝ) + 1) * mu = (η / 2) / 2 := by
        field_simp
        try ring
      rw [heq]
      linarith
    obtain ⟨M, hM, hM1⟩ : ∃ M : ℕ, r M < δ ∧ 1 ≤ M := by
      obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp
        (Filter.Tendsto.eventually_lt_const hδpos hrlim)
      exact ⟨max M0 1, lt_of_le_of_lt (hantitone (le_max_left M0 1)) (hM0 M0 (le_refl M0)),
        le_max_right _ _⟩
    set N' := max N (J + M) with hN'
    have hNN' : N ≤ N' := le_max_left _ _
    have hJM : J + M ≤ N' := le_max_right _ _
    -- uniform descent constants over the window `[J, N']`
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ j ∈ Finset.Icc J N', alp j + bet j ≤ C := by
      obtain ⟨C, hC⟩ := ((Finset.Icc J N').image (fun j => alp j + bet j)).exists_le
      exact ⟨C, fun j hj => hC _ (Finset.mem_image_of_mem _ hj)⟩
    have hC0 : 0 ≤ C := by
      rcases Nat.le_total J N' with h | h
      · have := hC J (Finset.mem_Icc.mpr ⟨le_refl J, h⟩)
        have h1 := halp J (hJ J (le_refl J))
        have h2 := hbet J (hJ J (le_refl J))
        linarith
      · have := hC N' (Finset.mem_Icc.mpr ⟨by omega, le_refl N'⟩)
        have h1 := halp N' (hJ N' (by omega))
        have h2 := hbet N' (hJ N' (by omega))
        linarith

    obtain ⟨ε, hεpos, hεsmall⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * C * mu < η / 2 := by
      refine ⟨(η / 2) / (2 * (C + 1) * mu), by positivity, ?_⟩
      have heq : (η / 2) / (2 * (C + 1) * mu) * C * mu = (η / 2) * (C / (C + 1)) / 2 := by
        field_simp
        try ring
      rw [heq]
      have h1 : C / (C + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h2 : (0:ℝ) ≤ C / (C + 1) := by positivity
      nlinarith [hη]
    obtain ⟨Nqm, hNqm⟩ : ∃ Nqm : ℕ, ∀ j ∈ Finset.Icc J N', Nq j ε ≤ Nqm := by
      obtain ⟨Nqm, hNqm⟩ := ((Finset.Icc J N').image (fun j => Nq j ε)).exists_le
      exact ⟨Nqm, fun j hj => hNqm _ (Finset.mem_image_of_mem _ hj)⟩
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, Nqm + N' + M ≤ n ∧ L - ε ≤ u n := by
      have hfr : ∃ᶠ n in Filter.atTop, L - ε < u n :=
        Filter.frequently_lt_of_lt_limsup hcobdd (by linarith)
      obtain ⟨n, hn⟩ := (hfr.and_eventually (Filter.eventually_ge_atTop (Nqm + N' + M))).exists
      exact ⟨n, hn.2, le_of_lt hn.1⟩
    -- descent gives bounds on the window `[J, N']`
    have hwin : ∀ j : ℕ, J ≤ j → j ≤ N' → L - ε * C ≤ u (n - j) := by
      intro j hj1 hj2
      have hmemj : j ∈ Finset.Icc J N' := Finset.mem_Icc.mpr ⟨hj1, hj2⟩
      have hnj : Nq j ε ≤ n := le_trans (hNqm j hmemj) (by omega)
      have h := hNq j (hJ j hj1) ε hεpos n hnj ε hn2
      have hCj := hC j hmemj
      have hrw : alp j * ε + bet j * ε = (alp j + bet j) * ε := by ring
      rw [hrw] at h
      have : (alp j + bet j) * ε ≤ C * ε := mul_le_mul_of_nonneg_right hCj (le_of_lt hεpos)
      nlinarith [h, this]
    -- downward induction reaches the finitely many indices below `J`
    have hdown : ∀ i : ℕ, ∀ j : ℕ, J - i ≤ j → j ≤ N' →
        L - (ε * C + (i:ℝ) * δ) ≤ u (n - j) := by
      intro i
      induction i with
      | zero =>
          intro j hj1 hj2
          have hjJ : J ≤ j := by omega
          have h := hwin j hjJ hj2
          push_cast
          linarith
      | succ i ih =>
          intro j hj1 hj2
          by_cases hcase : J - i ≤ j
          · have h := ih j hcase hj2
            push_cast at h ⊢
            nlinarith [h, hδpos]
          · have hjval : j + 1 = J - i := by omega
            have hjlt : j < J := by omega
            by_cases hneg : L - (ε * C + (i:ℝ) * δ) ≤ 0
            · have : L - (ε * C + ((i:ℝ) + 1) * δ) ≤ 0 := by nlinarith [hδpos]
              push_cast
              linarith [hunn (n - j)]
            · push_neg at hneg
              have hnj1 : 1 ≤ n - j := by omega
              have hnjM : M ≤ n - j := by omega
              have hurm : u (n - j)
                  = ∑ k ∈ Finset.range (n - j), f (k + 1) * u (n - j - 1 - k) := by
                have h := hurec (n - j - 1)
                have e : n - j - 1 + 1 = n - j := by omega
                rw [e] at h
                exact h
              have hsub : Finset.range M ⊆ Finset.range (n - j) :=
                fun k hk => by rw [Finset.mem_range] at hk ⊢; omega
              have hlow : ∑ k ∈ Finset.range M, f (k + 1) * u (n - j - 1 - k)
                  ≤ u (n - j) := by
                rw [hurm]
                exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun k _ _ => mul_nonneg (hf _) (hunn _))
              have hterm : ∀ k ∈ Finset.range M,
                  f (k + 1) * (L - (ε * C + (i:ℝ) * δ)) ≤ f (k + 1) * u (n - j - 1 - k) := by
                intro k hk
                rw [Finset.mem_range] at hk
                refine mul_le_mul_of_nonneg_left ?_ (hf _)
                have he : n - j - 1 - k = n - (j + k + 1) := by omega
                rw [he]
                exact ih (j + k + 1) (by omega) (by omega)
              have hsum2 : (∑ k ∈ Finset.range M, f (k + 1)) * (L - (ε * C + (i:ℝ) * δ))
                  ≤ u (n - j) := by
                calc (∑ k ∈ Finset.range M, f (k + 1)) * (L - (ε * C + (i:ℝ) * δ))
                    = ∑ k ∈ Finset.range M, f (k + 1) * (L - (ε * C + (i:ℝ) * δ)) := by
                      rw [Finset.sum_mul]
                  _ ≤ ∑ k ∈ Finset.range M, f (k + 1) * u (n - j - 1 - k) :=
                      Finset.sum_le_sum hterm
                  _ ≤ u (n - j) := hlow
              rw [hpart M, sub_mul, one_mul] at hsum2
              have hX1 : L - (ε * C + (i:ℝ) * δ) ≤ 1 := by
                have hnn : 0 ≤ ε * C + (i:ℝ) * δ := by positivity
                linarith
              have hprod : r M * (L - (ε * C + (i:ℝ) * δ)) ≤ δ := by
                calc r M * (L - (ε * C + (i:ℝ) * δ)) ≤ r M * 1 :=
                      mul_le_mul_of_nonneg_left hX1 (hrnn M)
                  _ = r M := by ring
                  _ ≤ δ := le_of_lt hM
              push_cast
              linarith [hsum2, hprod]
    -- assemble
    have hall : ∀ j : ℕ, j ≤ N' → L - (ε * C + (J:ℝ) * δ) ≤ u (n - j) :=
      fun j hj => hdown J j (by omega) hj
    have hsubset : Finset.range (N' + 1) ⊆ Finset.range (n + 1) :=
      fun j hj => by rw [Finset.mem_range] at hj ⊢; omega
    have hfin : (L - (ε * C + (J:ℝ) * δ)) * (∑ j ∈ Finset.range (N' + 1), r j) ≤ 1 := by
      calc (L - (ε * C + (J:ℝ) * δ)) * ∑ j ∈ Finset.range (N' + 1), r j
          = ∑ j ∈ Finset.range (N' + 1), (L - (ε * C + (J:ℝ) * δ)) * r j := by
            rw [Finset.mul_sum]
        _ ≤ ∑ j ∈ Finset.range (N' + 1), u (n - j) * r j :=
            Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right
              (hall j (by rw [Finset.mem_range] at hj; omega)) (hrnn j))
        _ ≤ ∑ j ∈ Finset.range (n + 1), u (n - j) * r j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun j _ _ => mul_nonneg (hunn _) (hrnn _))
        _ = 1 := hid2 n
    have hTle : ∑ j ∈ Finset.range (N' + 1), r j ≤ mu := hpartle _
    have hTnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (N' + 1), r j :=
      Finset.sum_nonneg (fun j _ => hrnn j)
    have hmono : ∑ j ∈ Finset.range (N + 1), r j ≤ ∑ j ∈ Finset.range (N' + 1), r j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => by rw [Finset.mem_range] at hj ⊢; omega) (fun j _ _ => hrnn j)
    have hEnn : 0 ≤ ε * C + (J:ℝ) * δ := by positivity
    nlinarith [hfin, hTle, hTnn, hmono, hL0, hεsmall, hδsmall, hmupos, hEnn]
  have hLmu : L * mu ≤ 1 := by
    have h2 : Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (N + 1), r j)
        Filter.atTop (nhds mu) :=
      hmean.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact le_of_tendsto (h2.const_mul L) (Filter.Eventually.of_forall hLkey)
  -- the mirror argument for the liminf
  set l := Filter.liminf u Filter.atTop with hldef
  have hbdd2 : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n using hunn n
  have hcobdd2 : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u := by
    refine ⟨1, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact le_trans hn (hule n)
  have hl1 : l ≤ 1 :=
    Filter.liminf_le_of_frequently_le
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hule)) hbdd2
  have hl0 : 0 ≤ l :=
    Filter.le_liminf_of_le hcobdd2 (Filter.Eventually.of_forall hunn)
  -- one ascent step
  have honestep2 : ∀ a : ℕ, 0 < f a → 1 ≤ a → ∀ ε : ℝ, 0 < ε →
      ∃ Nq : ℕ, ∀ m : ℕ, Nq ≤ m → ∀ b : ℝ, u m ≤ l + b →
        u (m - a) ≤ l + (b + 2 * ε) / f a := by
    intro a hfa ha1 ε hε
    have hfa1 : f a ≤ 1 := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      have h1 : f (c + 1) ≤ ∑ k ∈ Finset.range (c + 1), f (k + 1) :=
        Finset.single_le_sum (f := fun k => f (k + 1)) (fun k _ => hf _)
          (Finset.self_mem_range_succ c)
      exact h1.trans (hfsum_le (c + 1))
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (Filter.eventually_lt_of_lt_liminf (show l - ε < l by linarith) hbdd2)
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
      (Filter.Tendsto.eventually_lt_const hε hrlim)
    refine ⟨N0 + N2 + a, fun m hm b hb => ?_⟩
    have hm1 : m - 1 + 1 = m := by omega
    have hurm : u m = ∑ k ∈ Finset.range m, f (k + 1) * u (m - 1 - k) := by
      have h := hurec (m - 1)
      rw [hm1] at h
      exact h
    have hsplit : ∑ k ∈ Finset.range m, f (k + 1) * u (m - 1 - k)
        = (∑ k ∈ Finset.range (m - N0), f (k + 1) * u (m - 1 - k))
          + ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) * u (m - 1 - k) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le (m - N0)) (by omega)]
    have htail2 : 0 ≤ ∑ k ∈ Finset.Ico (m - N0) m, f (k + 1) * u (m - 1 - k) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hf _) (hunn _))
    have hAmem : a - 1 ∈ Finset.range (m - N0) := by
      rw [Finset.mem_range]; omega
    have hAeq : f (a - 1 + 1) * u (m - 1 - (a - 1)) = f a * u (m - a) := by
      have e1 : a - 1 + 1 = a := by omega
      have e2 : m - 1 - (a - 1) = m - a := by omega
      rw [e1, e2]
    have hrestsum : ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1)
        = (1 - r (m - N0)) - f a := by
      have h3 : f (a - 1 + 1)
          + ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1)
          = ∑ k ∈ Finset.range (m - N0), f (k + 1) :=
        Finset.add_sum_erase (Finset.range (m - N0)) (fun k => f (k + 1)) hAmem
      have e1 : a - 1 + 1 = a := by omega
      rw [e1, hpart] at h3
      linarith
    have hrest : ((1 - r (m - N0)) - f a) * (l - ε)
        ≤ ∑ k ∈ (Finset.range (m - N0)).erase (a - 1), f (k + 1) * u (m - 1 - k) := by
      rw [← hrestsum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_erase, Finset.mem_range] at hk
      exact mul_le_mul_of_nonneg_left (le_of_lt (hN0 (m - 1 - k) (by omega))) (hf _)
    have hmain0 : f a * u (m - a) + ((1 - r (m - N0)) - f a) * (l - ε)
        ≤ ∑ k ∈ Finset.range (m - N0), f (k + 1) * u (m - 1 - k) := by
      rw [← Finset.add_sum_erase (Finset.range (m - N0))
        (fun k => f (k + 1) * u (m - 1 - k)) hAmem, hAeq]
      linarith
    have hrsmall : r (m - N0) < ε := hN2 (m - N0) (by omega)
    have hrnn2 : 0 ≤ r (m - N0) := hrnn _
    have habs : r (m - N0) * (l - ε) ≤ ε := by
      rcases le_or_gt 0 (l - ε) with h | h
      · calc r (m - N0) * (l - ε) ≤ r (m - N0) * 1 :=
              mul_le_mul_of_nonneg_left (by linarith [hl1]) hrnn2
          _ = r (m - N0) := by ring
          _ ≤ ε := le_of_lt hrsmall
      · nlinarith [mul_nonneg hrnn2 (neg_nonneg.mpr (le_of_lt h)), hε]
    have hexp : ((1 - r (m - N0)) - f a) * (l - ε)
        = (1 - f a) * (l - ε) - r (m - N0) * (l - ε) := by ring
    have hfinal : f a * u (m - a) + (1 - f a) * (l - ε) - ε ≤ u m := by
      rw [hurm, hsplit]
      rw [hexp] at hmain0
      linarith [hmain0, htail2, habs]
    have he2 : (1 - f a) * (l - ε) = l - ε - f a * l + f a * ε := by ring
    have he3 : f a * (u (m - a) - l) = f a * u (m - a) - f a * l := by ring
    have hstar : f a * (u (m - a) - l) ≤ b + 2 * ε := by
      rw [he2] at hfinal
      rw [he3]
      linarith [hfinal, hb, mul_nonneg (le_of_lt hfa) (le_of_lt hε)]
    have h2 : u (m - a) - l ≤ (b + 2 * ε) / f a := (le_div_iff₀ hfa).mpr (by linarith [hstar])
    linarith
  have hQ2 : ∀ m : ℕ, m ∈ AddSubmonoid.closure Sset →
      ∃ α β : ℝ, 0 < α ∧ 0 ≤ β ∧ ∀ ε : ℝ, 0 < ε → ∃ Nq : ℕ, ∀ n : ℕ, Nq ≤ n →
        ∀ b : ℝ, u n ≤ l + b → u (n - m) ≤ l + (α * b + β * ε) := by
    intro m hm
    refine AddSubmonoid.closure_induction ?_ ?_ ?_ hm
    · intro x hx
      obtain ⟨hfx, hx1⟩ := hx
      refine ⟨(f x)⁻¹, 2 * (f x)⁻¹, by positivity, by positivity, fun ε hε => ?_⟩
      obtain ⟨Nqa, hNqa⟩ := honestep2 x hfx hx1 ε hε
      refine ⟨Nqa, fun n hn b hb => ?_⟩
      have h := hNqa n hn b hb
      have hrw : (b + 2 * ε) / f x = (f x)⁻¹ * b + 2 * (f x)⁻¹ * ε := by
        field_simp
        try ring
      rwa [hrw] at h
    · refine ⟨1, 0, one_pos, le_refl 0, fun ε hε => ⟨0, fun n _ b hb => ?_⟩⟩
      rw [Nat.sub_zero]
      linarith
    · rintro x y - - ⟨α₁, β₁, hα₁, hβ₁, hx⟩ ⟨α₂, β₂, hα₂, hβ₂, hy⟩
      refine ⟨α₂ * α₁, α₂ * β₁ + β₂, by positivity, by positivity, fun ε hε => ?_⟩
      obtain ⟨Nq₁, hNq₁⟩ := hx ε hε
      obtain ⟨Nq₂, hNq₂⟩ := hy ε hε
      refine ⟨max Nq₁ (Nq₂ + x), fun n hn b hb => ?_⟩
      have hn1 : Nq₁ ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : Nq₂ ≤ n - x := by
        have := le_trans (le_max_right _ _) hn
        omega
      have h1 := hNq₁ n hn1 b hb
      have h2 := hNq₂ (n - x) hn2 (α₁ * b + β₁ * ε) h1
      have hsubx : n - x - y = n - (x + y) := by omega
      rw [hsubx] at h2
      calc u (n - (x + y)) ≤ l + (α₂ * (α₁ * b + β₁ * ε) + β₂ * ε) := h2
        _ = l + (α₂ * α₁ * b + (α₂ * β₁ + β₂) * ε) := by ring
  choose! alp2 bet2 halp2 hbet2 hQ2' using hQ2
  choose! Nq2 hNq2 using hQ2'
  have hlkey : 1 ≤ l * mu := by
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ((J:ℝ) + 1) * mu < η / 3 := by
      refine ⟨(η / 3) / (2 * ((J:ℝ) + 1) * mu), by positivity, ?_⟩
      have heq : (η / 3) / (2 * ((J:ℝ) + 1) * mu) * ((J:ℝ) + 1) * mu = (η / 3) / 2 := by
        field_simp
        try ring
      rw [heq]
      linarith
    obtain ⟨M, hM, hM1⟩ : ∃ M : ℕ, r M < δ ∧ 1 ≤ M := by
      obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp
        (Filter.Tendsto.eventually_lt_const hδpos hrlim)
      exact ⟨max M0 1, lt_of_le_of_lt (hantitone (le_max_left M0 1)) (hM0 M0 (le_refl M0)),
        le_max_right _ _⟩
    obtain ⟨N3, hN3⟩ := htail (η / 3) (by linarith)
    set N' := max N3 (J + M) with hN'
    have hN3' : N3 ≤ N' := le_max_left _ _
    have hJM : J + M ≤ N' := le_max_right _ _
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ j ∈ Finset.Icc J N', alp2 j + bet2 j ≤ C := by
      obtain ⟨C, hC⟩ := ((Finset.Icc J N').image (fun j => alp2 j + bet2 j)).exists_le
      exact ⟨C, fun j hj => hC _ (Finset.mem_image_of_mem _ hj)⟩
    have hC0 : 0 ≤ C := by
      have hmem : J ∈ Finset.Icc J N' := Finset.mem_Icc.mpr ⟨le_refl J, by omega⟩
      have h0 := hC J hmem
      have h1 := halp2 J (hJ J (le_refl J))
      have h2 := hbet2 J (hJ J (le_refl J))
      linarith
    obtain ⟨ε, hεpos, hεsmall⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * C * mu < η / 3 := by
      refine ⟨(η / 3) / (2 * (C + 1) * mu), by positivity, ?_⟩
      have heq : (η / 3) / (2 * (C + 1) * mu) * C * mu = (η / 3) * (C / (C + 1)) / 2 := by
        field_simp
        try ring
      rw [heq]
      have h1 : C / (C + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h2 : (0:ℝ) ≤ C / (C + 1) := by positivity
      nlinarith [hη]
    obtain ⟨Nqm, hNqm⟩ : ∃ Nqm : ℕ, ∀ j ∈ Finset.Icc J N', Nq2 j ε ≤ Nqm := by
      obtain ⟨Nqm, hNqm⟩ := ((Finset.Icc J N').image (fun j => Nq2 j ε)).exists_le
      exact ⟨Nqm, fun j hj => hNqm _ (Finset.mem_image_of_mem _ hj)⟩
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, Nqm + N' + M ≤ n ∧ u n ≤ l + ε := by
      have hfr : ∃ᶠ n in Filter.atTop, u n < l + ε :=
        Filter.frequently_lt_of_liminf_lt hcobdd2 (by linarith)
      obtain ⟨n, hn⟩ := (hfr.and_eventually (Filter.eventually_ge_atTop (Nqm + N' + M))).exists
      exact ⟨n, hn.2, le_of_lt hn.1⟩
    have hwin : ∀ j : ℕ, J ≤ j → j ≤ N' → u (n - j) ≤ l + ε * C := by
      intro j hj1 hj2
      have hmemj : j ∈ Finset.Icc J N' := Finset.mem_Icc.mpr ⟨hj1, hj2⟩
      have hnj : Nq2 j ε ≤ n := le_trans (hNqm j hmemj) (by omega)
      have h := hNq2 j (hJ j hj1) ε hεpos n hnj ε hn2
      have hCj := hC j hmemj
      have hrw : alp2 j * ε + bet2 j * ε = (alp2 j + bet2 j) * ε := by ring
      rw [hrw] at h
      have hle2 : (alp2 j + bet2 j) * ε ≤ C * ε :=
        mul_le_mul_of_nonneg_right hCj (le_of_lt hεpos)
      nlinarith [h, hle2]
    have hdown : ∀ i : ℕ, ∀ j : ℕ, J - i ≤ j → j ≤ N' →
        u (n - j) ≤ l + (ε * C + (i:ℝ) * δ) := by
      intro i
      induction i with
      | zero =>
          intro j hj1 hj2
          have hjJ : J ≤ j := by omega
          have h := hwin j hjJ hj2
          push_cast
          linarith
      | succ i ih =>
          intro j hj1 hj2
          by_cases hcase : J - i ≤ j
          · have h := ih j hcase hj2
            push_cast at h ⊢
            nlinarith [h, hδpos]
          · have hjlt : j < J := by omega
            have hnj1 : 1 ≤ n - j := by omega
            have hnjM : M ≤ n - j := by omega
            have hurm : u (n - j)
                = ∑ k ∈ Finset.range (n - j), f (k + 1) * u (n - j - 1 - k) := by
              have h := hurec (n - j - 1)
              have e : n - j - 1 + 1 = n - j := by omega
              rw [e] at h
              exact h
            have hsplit2 : ∑ k ∈ Finset.range (n - j), f (k + 1) * u (n - j - 1 - k)
                = (∑ k ∈ Finset.range M, f (k + 1) * u (n - j - 1 - k))
                  + ∑ k ∈ Finset.Ico M (n - j), f (k + 1) * u (n - j - 1 - k) := by
              rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
                Finset.sum_Ico_consecutive _ (Nat.zero_le M) hnjM]
            have hEnn : 0 ≤ ε * C + (i:ℝ) * δ := by positivity
            have hhead : ∑ k ∈ Finset.range M, f (k + 1) * u (n - j - 1 - k)
                ≤ l + (ε * C + (i:ℝ) * δ) := by
              have h1 : ∑ k ∈ Finset.range M, f (k + 1) * u (n - j - 1 - k)
                  ≤ ∑ k ∈ Finset.range M, f (k + 1) * (l + (ε * C + (i:ℝ) * δ)) := by
                refine Finset.sum_le_sum (fun k hk => ?_)
                rw [Finset.mem_range] at hk
                refine mul_le_mul_of_nonneg_left ?_ (hf _)
                have he : n - j - 1 - k = n - (j + k + 1) := by omega
                rw [he]
                exact ih (j + k + 1) (by omega) (by omega)
              have h2 : ∑ k ∈ Finset.range M, f (k + 1) * (l + (ε * C + (i:ℝ) * δ))
                  = (∑ k ∈ Finset.range M, f (k + 1)) * (l + (ε * C + (i:ℝ) * δ)) := by
                rw [Finset.sum_mul]
              rw [h2, hpart M] at h1
              have h3 : (1 - r M) * (l + (ε * C + (i:ℝ) * δ))
                  ≤ l + (ε * C + (i:ℝ) * δ) := by
                nlinarith [hrnn M, hl0, hEnn]
              linarith
            have htl : ∑ k ∈ Finset.Ico M (n - j), f (k + 1) * u (n - j - 1 - k) ≤ δ := by
              have h1 : ∑ k ∈ Finset.Ico M (n - j), f (k + 1) * u (n - j - 1 - k)
                  ≤ ∑ k ∈ Finset.Ico M (n - j), f (k + 1) := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                calc f (k + 1) * u (n - j - 1 - k) ≤ f (k + 1) * 1 :=
                      mul_le_mul_of_nonneg_left (hule _) (hf _)
                  _ = f (k + 1) := by ring
              have h2 : ∑ k ∈ Finset.Ico M (n - j), f (k + 1)
                  = (∑ k ∈ Finset.range (n - j), f (k + 1))
                    - ∑ k ∈ Finset.range M, f (k + 1) := by
                rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
                  ← Finset.sum_Ico_consecutive (fun k => f (k + 1)) (Nat.zero_le M) hnjM]
                ring
              rw [h2, hpart, hpart] at h1
              linarith [hrnn (n - j), le_of_lt hM]
            rw [hurm, hsplit2]
            push_cast
            linarith [hhead, htl]
    have hall : ∀ j : ℕ, j ≤ N' → u (n - j) ≤ l + (ε * C + (J:ℝ) * δ) :=
      fun j hj => hdown J j (by omega) hj
    have hEnn2 : (0:ℝ) ≤ ε * C + (J:ℝ) * δ := by positivity
    have hsplit3 : ∑ j ∈ Finset.range (n + 1), u (n - j) * r j
        = (∑ j ∈ Finset.range (N' + 1), u (n - j) * r j)
          + ∑ j ∈ Finset.Ico (N' + 1) (n + 1), u (n - j) * r j := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le (N' + 1)) (by omega)]
    have hhead2 : ∑ j ∈ Finset.range (N' + 1), u (n - j) * r j
        ≤ (l + (ε * C + (J:ℝ) * δ)) * mu := by
      have h1 : ∑ j ∈ Finset.range (N' + 1), u (n - j) * r j
          ≤ ∑ j ∈ Finset.range (N' + 1), (l + (ε * C + (J:ℝ) * δ)) * r j :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right
          (hall j (by rw [Finset.mem_range] at hj; omega)) (hrnn j))
      have h2 : ∑ j ∈ Finset.range (N' + 1), (l + (ε * C + (J:ℝ) * δ)) * r j
          = (l + (ε * C + (J:ℝ) * δ)) * ∑ j ∈ Finset.range (N' + 1), r j := by
        rw [Finset.mul_sum]
      rw [h2] at h1
      have h3 : (l + (ε * C + (J:ℝ) * δ)) * ∑ j ∈ Finset.range (N' + 1), r j
          ≤ (l + (ε * C + (J:ℝ) * δ)) * mu :=
        mul_le_mul_of_nonneg_left (hpartle _) (by linarith)
      linarith
    have htl2 : ∑ j ∈ Finset.Ico (N' + 1) (n + 1), u (n - j) * r j ≤ η / 3 := by
      have h1 : ∑ j ∈ Finset.Ico (N' + 1) (n + 1), u (n - j) * r j
          ≤ ∑ j ∈ Finset.Ico (N' + 1) (n + 1), r j := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        calc u (n - j) * r j ≤ 1 * r j :=
              mul_le_mul_of_nonneg_right (hule _) (hrnn j)
          _ = r j := by ring
      have h2 : ∑ j ∈ Finset.Ico (N' + 1) (n + 1), r j
          = (∑ j ∈ Finset.range (n + 1), r j) - ∑ j ∈ Finset.range (N' + 1), r j := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive r (Nat.zero_le (N' + 1)) (by omega)]
        ring
      have h3 : ∑ j ∈ Finset.range (n + 1), r j ≤ mu := hpartle _
      have h4 : mu - ∑ j ∈ Finset.range (N3), r j < η / 3 := hN3
      have h5 : ∑ j ∈ Finset.range N3, r j ≤ ∑ j ∈ Finset.range (N' + 1), r j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj => by rw [Finset.mem_range] at hj ⊢; omega) (fun j _ _ => hrnn j)
      rw [h2] at h1
      linarith
    have hone : (1:ℝ) ≤ (l + (ε * C + (J:ℝ) * δ)) * mu + η / 3 := by
      rw [← hid2 n, hsplit3]
      linarith [hhead2, htl2]
    have hexpand : (l + (ε * C + (J:ℝ) * δ)) * mu = l * mu + ε * C * mu + (J:ℝ) * δ * mu := by
      ring
    have hJδ : (J:ℝ) * δ * mu ≤ δ * ((J:ℝ) + 1) * mu := by
      have : (0:ℝ) ≤ mu := le_of_lt hmupos
      nlinarith [hδpos, Nat.cast_nonneg (α := ℝ) J]
    rw [hexpand] at hone
    linarith [hone, hεsmall, hδsmall, hJδ]
  -- conclude
  have hLle : L ≤ 1 / mu := by
    rw [le_div_iff₀ hmupos]
    linarith [hLmu]
  have hlge : 1 / mu ≤ l := by
    rw [div_le_iff₀ hmupos]
    linarith [hlkey]
  have hlL : l ≤ L := Filter.liminf_le_limsup hbdd hbdd2
  have hLeq : L = 1 / mu := le_antisymm hLle (le_trans hlge hlL)
  have hleq : l = 1 / mu := le_antisymm (le_trans hlL hLle) hlge
  exact tendsto_of_le_liminf_of_limsup_le (le_of_eq hleq.symm) (le_of_eq hLeq) hbdd hbdd2
