-- Prove2me | solution 1 for Renewal.renewal_null_limit
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T17:50:36.976022+00:00
-- url     : https://prove2.me/submissions/fcf5c43f-3cb6-4137-b84f-3cb10a490490

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter Finset
open scoped Topology

/-- **Erdős–Feller–Pollard, null case.**  `f (k+1)` is the probability that the
first renewal happens at time `k+1`, `r n = ∑_{k > n} f k` is the tail of that
law, and `u` is the renewal sequence.  If the mean renewal time is infinite
(`r` not summable) and the law is proper (`r → 0`), then `u n → 0`. -/
theorem solution (f r u : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hstep : ∀ n : ℕ, r n = r (n + 1) + f (n + 1))
    (hr0 : r 0 = 1)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (hrsum : ¬ Summable r)
    (hu0 : u 0 = 1)
    (hurec : ∀ n : ℕ, u (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
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
  -- there is a step size `A` with positive probability
  have hexA : ∃ A : ℕ, 1 ≤ A ∧ 0 < f A := by
    by_contra hc
    push_neg at hc
    have hz : ∀ k : ℕ, f (k + 1) = 0 := by
      intro k
      have h1 := hc (k + 1) (by omega)
      linarith [hf (k + 1)]
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
  obtain ⟨A, hA1, hAf⟩ := hexA
  have hAf1 : f A ≤ 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    have h1 : f (a + 1) ≤ ∑ k ∈ Finset.range (a + 1), f (k + 1) :=
      Finset.single_le_sum (f := fun k => f (k + 1)) (fun k _ => hf _)
        (Finset.self_mem_range_succ a)
    exact h1.trans (hfsum_le (a + 1))
  -- partial sums along the arithmetic progression `A * k` are unbounded
  have hblock : ∀ N : ℕ,
      ∑ j ∈ Finset.range (A * N), r j ≤ (A : ℝ) * ∑ k ∈ Finset.range N, r (A * k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have hmul : A * (N + 1) = A * N + A := by ring
        have hsplit : ∑ j ∈ Finset.range (A * N + A), r j
            = (∑ j ∈ Finset.range (A * N), r j)
              + ∑ j ∈ Finset.Ico (A * N) (A * N + A), r j := by
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
            Finset.sum_Ico_consecutive _ (Nat.zero_le (A * N)) (by omega)]
        have hb : ∑ j ∈ Finset.Ico (A * N) (A * N + A), r j ≤ (A : ℝ) * r (A * N) := by
          have h1 : ∑ j ∈ Finset.Ico (A * N) (A * N + A), r j
              ≤ ∑ _j ∈ Finset.Ico (A * N) (A * N + A), r (A * N) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [Finset.mem_Ico] at hj
            exact hantitone hj.1
          refine h1.trans (le_of_eq ?_)
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          congr 1
          congr 1
          omega
        rw [hmul, hsplit, Finset.sum_range_succ, mul_add]
        linarith [ih, hb]
  have hARunbdd : ∀ C : ℝ, ∃ K : ℕ, C ≤ ∑ k ∈ Finset.range (K + 1), r (A * k) := by
    intro C
    have hten := (not_summable_iff_tendsto_nat_atTop_of_nonneg hrnn).mp hrsum
    obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp hten ((A : ℝ) * C))
    refine ⟨N', ?_⟩
    have hle : N' + 1 ≤ A * (N' + 1) := by
      have h0 : 1 * (N' + 1) ≤ A * (N' + 1) := Nat.mul_le_mul_right _ hA1
      rw [one_mul] at h0
      exact h0
    have hsub : Finset.range N' ⊆ Finset.range (A * (N' + 1)) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      exact hx.trans_le (le_trans (Nat.le_succ N') hle)
    have hmono : ∑ j ∈ Finset.range N', r j ≤ ∑ j ∈ Finset.range (A * (N' + 1)), r j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hrnn j)
    have h1 : (A : ℝ) * C ≤ ∑ j ∈ Finset.range (A * (N' + 1)), r j :=
      le_trans (hN' N' (le_refl _)) hmono
    have h2 := hblock (N' + 1)
    have hApos : (0:ℝ) < A := by exact_mod_cast hA1
    exact le_of_mul_le_mul_left (le_trans h1 h2) hApos
  -- the reflected renewal identity
  have hid2 : ∀ n, ∑ j ∈ Finset.range (n + 1), u (n - j) * r j = 1 := by
    intro n
    rw [← hid n, ← Finset.sum_range_reflect (fun j => u j * r (n - j)) (n + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have e1 : n + 1 - 1 - j = n - j := by omega
    have e2 : n - (n - j) = j := by omega
    rw [e1, e2]
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
  -- the compounding constants
  set c : ℕ → ℝ := fun j => Nat.rec (1:ℝ) (fun _ x => (x + 2) / f A) j with hcdef
  have hc0 : c 0 = 1 := rfl
  have hcsucc : ∀ j, c (j + 1) = (c j + 2) / f A := fun _ => rfl
  have hcpos : ∀ j, 0 < c j := by
    intro j
    induction j with
    | zero => rw [hc0]; norm_num
    | succ j ih => rw [hcsucc]; positivity
  have hcmono : Monotone c := by
    refine monotone_nat_of_le_succ (fun j => ?_)
    rw [hcsucc, le_div_iff₀ hAf]
    nlinarith [hcpos j, hAf1, hAf]
  -- key bound
  have hkey : ∀ K : ℕ, L * (∑ k ∈ Finset.range (K + 1), r (A * k)) ≤ 1 := by
    intro K
    have hRK0 : (0:ℝ) ≤ ∑ k ∈ Finset.range (K + 1), r (A * k) :=
      Finset.sum_nonneg (fun k _ => hrnn _)
    have hmain : ∀ ε : ℝ, 0 < ε →
        (L - ε * c K) * (∑ k ∈ Finset.range (K + 1), r (A * k)) ≤ 1 := by
      intro ε hε
      obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
        (Filter.eventually_lt_of_limsup_lt (show L < L + ε by linarith) hbdd)
      obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
        (Filter.Tendsto.eventually_lt_const hε hrlim)
      -- one descent step
      have hstepdown : ∀ m : ℕ, N0 + N2 + A ≤ m → ∀ b : ℝ, L - b ≤ u m →
          L - (b + 2 * ε) / f A ≤ u (m - A) := by
        intro m hm b hb
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
        have hAmem : A - 1 ∈ Finset.range (m - N0) := by
          rw [Finset.mem_range]; omega
        have hAeq : f (A - 1 + 1) * u (m - 1 - (A - 1)) = f A * u (m - A) := by
          have e1 : A - 1 + 1 = A := by omega
          have e2 : m - 1 - (A - 1) = m - A := by omega
          rw [e1, e2]
        have hmain0 : ∑ k ∈ Finset.range (m - N0), f (k + 1) * u (m - 1 - k)
            ≤ f A * u (m - A) + (L + ε) * (1 - f A) := by
          rw [← Finset.add_sum_erase (Finset.range (m - N0))
            (fun k => f (k + 1) * u (m - 1 - k)) hAmem, hAeq]
          have hrest : ∑ k ∈ (Finset.range (m - N0)).erase (A - 1),
                f (k + 1) * u (m - 1 - k)
              ≤ (L + ε) * (1 - f A) := by
            have h1 : ∑ k ∈ (Finset.range (m - N0)).erase (A - 1),
                  f (k + 1) * u (m - 1 - k)
                ≤ ∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1) * (L + ε) := by
              refine Finset.sum_le_sum (fun k hk => ?_)
              rw [Finset.mem_erase, Finset.mem_range] at hk
              refine mul_le_mul_of_nonneg_left (le_of_lt (hN0 (m - 1 - k) ?_)) (hf _)
              omega
            have h2 : ∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1)
                ≤ 1 - f A := by
              have h3 : f (A - 1 + 1)
                  + ∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1)
                  = ∑ k ∈ Finset.range (m - N0), f (k + 1) :=
                Finset.add_sum_erase (Finset.range (m - N0)) (fun k => f (k + 1)) hAmem
              have e1 : A - 1 + 1 = A := by omega
              rw [e1, hpart] at h3
              linarith [hrnn (m - N0)]
            calc ∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1) * u (m - 1 - k)
                ≤ ∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1) * (L + ε) := h1
              _ = (∑ k ∈ (Finset.range (m - N0)).erase (A - 1), f (k + 1)) * (L + ε) := by
                  rw [Finset.sum_mul]
              _ ≤ (1 - f A) * (L + ε) := by
                  refine mul_le_mul_of_nonneg_right h2 (by linarith)
              _ = (L + ε) * (1 - f A) := by ring
          linarith
        have hfinal : L - b ≤ f A * u (m - A) + (L + ε) * (1 - f A) + ε := by
          rw [hurm, hsplit] at hb
          linarith
        have hstar : (L - u (m - A)) * f A ≤ b + 2 * ε := by nlinarith [hfinal, hAf, hε]
        have h2 : L - u (m - A) ≤ (b + 2 * ε) / f A := (le_div_iff₀ hAf).mpr hstar
        linarith
      -- iterate the descent
      have hiter : ∀ n : ℕ, N0 + N2 + A + K * A ≤ n → L - ε ≤ u n →
          ∀ j : ℕ, j ≤ K → L - ε * c j ≤ u (n - j * A) := by
        intro n hn hun j
        induction j with
        | zero =>
            intro _
            rw [hc0, Nat.zero_mul, Nat.sub_zero]
            linarith
        | succ j ih =>
            intro hjK
            have hj : j ≤ K := by omega
            have hprev := ih hj
            have hjA : j * A ≤ K * A := Nat.mul_le_mul_right A hj
            have hmge : N0 + N2 + A ≤ n - j * A := by omega
            have hstep2 := hstepdown (n - j * A) hmge (ε * c j) hprev
            have hexp : (j + 1) * A = j * A + A := by ring
            have heq : n - j * A - A = n - (j + 1) * A := by omega
            rw [heq] at hstep2
            have hcc : (ε * c j + 2 * ε) / f A = ε * c (j + 1) := by
              rw [hcsucc]
              field_simp
              try ring
            rw [hcc] at hstep2
            exact hstep2
      -- choose a good `n`
      obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, N0 + N2 + A + K * A ≤ n ∧ L - ε ≤ u n := by
        have hfr : ∃ᶠ n in Filter.atTop, L - ε < u n :=
          Filter.frequently_lt_of_lt_limsup hcobdd (by linarith)
        obtain ⟨n, hn⟩ := (hfr.and_eventually (Filter.eventually_ge_atTop
          (N0 + N2 + A + K * A))).exists
        exact ⟨n, hn.2, le_of_lt hn.1⟩
      have hemb : Function.Injective (fun k : ℕ => A * k) :=
        fun x y h => Nat.eq_of_mul_eq_mul_left hA1 h
      have hsub2 : (Finset.range (K + 1)).map ⟨fun k => A * k, hemb⟩
          ⊆ Finset.range (n + 1) := by
        intro j hj
        rw [Finset.mem_map] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        rw [Finset.mem_range] at hk
        rw [Finset.mem_range]
        show A * k < n + 1
        have h1 : A * k ≤ A * K := Nat.mul_le_mul_left A (by omega)
        have hKA : K * A = A * K := by ring
        omega
      have hmapeq : ∑ j ∈ (Finset.range (K + 1)).map ⟨fun k => A * k, hemb⟩,
            u (n - j) * r j
          = ∑ k ∈ Finset.range (K + 1), u (n - A * k) * r (A * k) :=
        Finset.sum_map _ _ _
      have hle1 : ∑ k ∈ Finset.range (K + 1), u (n - A * k) * r (A * k) ≤ 1 := by
        rw [← hid2 n, ← hmapeq]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
          (fun j _ _ => mul_nonneg (hunn _) (hrnn _))
      have hterm : ∀ k ∈ Finset.range (K + 1),
          (L - ε * c K) * r (A * k) ≤ u (n - A * k) * r (A * k) := by
        intro k hk
        rw [Finset.mem_range] at hk
        refine mul_le_mul_of_nonneg_right ?_ (hrnn _)
        have h1 := hiter n hn1 hn2 k (by omega)
        have h2 : ε * c k ≤ ε * c K :=
          mul_le_mul_of_nonneg_left (hcmono (by omega)) (le_of_lt hε)
        have hkA : k * A = A * k := by ring
        rw [hkA] at h1
        linarith
      calc (L - ε * c K) * (∑ k ∈ Finset.range (K + 1), r (A * k))
          = ∑ k ∈ Finset.range (K + 1), (L - ε * c K) * r (A * k) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ Finset.range (K + 1), u (n - A * k) * r (A * k) :=
            Finset.sum_le_sum hterm
        _ ≤ 1 := hle1
    -- let ε → 0
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    set D := c K * (∑ k ∈ Finset.range (K + 1), r (A * k)) with hD
    have hD0 : 0 ≤ D := mul_nonneg (le_of_lt (hcpos K)) hRK0
    have hεpos : 0 < δ / (D + 1) := by positivity
    have h := hmain (δ / (D + 1)) hεpos
    have hexp : (L - δ / (D + 1) * c K) * (∑ k ∈ Finset.range (K + 1), r (A * k))
        = L * (∑ k ∈ Finset.range (K + 1), r (A * k)) - δ / (D + 1) * D := by
      rw [hD]; ring
    rw [hexp] at h
    have hlast : δ / (D + 1) * D ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hD0, hδ]
    linarith
  -- conclude `L = 0`
  have hLle : L ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨K, hK⟩ := hARunbdd (2 / L)
    have h1 := hkey K
    have h2 : L * (2 / L) = 2 := by field_simp
    nlinarith [hK, hcon, h1, h2]
  have hLeq : L = 0 := le_antisymm hLle hL0
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.eventually_lt_of_limsup_lt (show L < ε by rw [hLeq]; exact hε) hbdd)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hunn n)]
  exact hN n hn
