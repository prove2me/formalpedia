-- Prove2me | solution 2 for CyclicTypeChannel.Ipair_lb_thirtyone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:03:51.131816+00:00
-- url     : https://prove2.me/submissions/dbd6d186-df81-4679-8bce-a73d2e92a5fe

import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannel.lean ====
/-
# The cyclic splitting-type channel

A self-contained, formally verified account of the *splitting-type channel* of a
cyclic field extension.

For a prime `f` the Galois group of `ℚ(ζ_f)/ℚ` is `(ℤ/f)ˣ ≅ C n` with `n = f - 1`.
Writing an unramified prime `p` as `g ^ a` for a fixed generator `g`, the residue
degree (= the order of the Frobenius `p mod f`) is

  `T(p) = ord_f(p) = n / gcd(a, n)`.

This file develops:

* a general finite (counting) Shannon-entropy framework `uEnt`, its conditional
  version `condEnt` and the mutual information `mutInfo`;
* the general structural facts: the Shannon form of `uEnt`, non-negativity, the
  `log₂ |s|` cap, and the *data-processing* inequality for deterministic
  coarsenings;
* the group-theoretic grounding: `orderOf (g ^ a) = ordType n a` for a generator
  `g` of a cyclic group of order `n`, and the exact type-count law
  `#{a : ordType n a = d} = φ d`;
* exact closed-form evaluations of the type channel and of the *type-pair
  channel* of a semiprime for `n = 2, 4, 6, 10, 12, 16`, culminating in the
  headline fact that the pair channel of `C₄` and `C₆` carries strictly more
  than one bit.
-/

namespace CyclicTypeChannel

open Finset

/-! ## 1. A counting Shannon-entropy framework -/

variable {α β γ : Type*}

-- [dropped: platform already declares uEnt]
-- [dropped: platform already declares condEnt]
-- [dropped: platform already declares mutInfo]
section General

variable [DecidableEq β] {s : Finset α} {g : α → β}

lemma fiber_card_pos {a : α} (ha : a ∈ s) : 0 < #{x ∈ s | g x = g a} :=
  card_pos.2 ⟨a, by simp [ha]⟩

lemma sum_fiber_card (s : Finset α) (g : α → β) :
    ∑ v ∈ s.image g, #{x ∈ s | g x = v} = s.card := by
  classical
  simpa using (Finset.sum_comp (fun _ : β => (1 : ℕ)) g).symm

/-- `uEnt` really is the Shannon entropy `-∑ p log₂ p` of the push-forward
distribution. -/
theorem uEnt_eq_shannon (hs : s.Nonempty) (g : α → β) :
    uEnt s g = ∑ v ∈ s.image g,
      -((#{x ∈ s | g x = v} : ℝ) / s.card) *
        Real.logb 2 ((#{x ∈ s | g x = v} : ℝ) / s.card) := by
  classical
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hA : ∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)
      = ∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    rw [Finset.sum_comp (fun v : β => Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) g]
    simp [nsmul_eq_mul]
  have hcard : ∑ v ∈ s.image g, ((#{x ∈ s | g x = v} : ℝ)) = (s.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s g)
  have hsplit : ∀ v ∈ s.image g,
      -((#{x ∈ s | g x = v} : ℝ) / s.card) *
        Real.logb 2 ((#{x ∈ s | g x = v} : ℝ) / s.card)
      = ((#{x ∈ s | g x = v} : ℝ) / s.card) * Real.logb 2 (s.card : ℝ)
        - ((#{x ∈ s | g x = v} : ℝ) / s.card) *
            Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    have hc : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    rw [Real.logb_div (ne_of_gt hc) (ne_of_gt hN)]
    ring
  have h2 : (∑ v ∈ s.image g,
        (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) / s.card
      = ∑ v ∈ s.image g,
        ((#{x ∈ s | g x = v} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [uEnt, hA, Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_div, hcard, h2, div_self (ne_of_gt hN), one_mul]

/-- Entropy is non-negative. -/
theorem uEnt_nonneg (s : Finset α) (g : α → β) : 0 ≤ uEnt s g := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ) ≤ Real.logb 2 (s.card : ℝ) := by
    intro a ha
    have hc : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    have : (#{x ∈ s | g x = g a} : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast card_filter_le s _
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) this
  have hsum : (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ))
      ≤ (s.card : ℝ) * Real.logb 2 (s.card : ℝ) := by
    calc (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ))
        ≤ ∑ _a ∈ s, Real.logb 2 (s.card : ℝ) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * Real.logb 2 (s.card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  rw [uEnt, sub_nonneg, div_le_iff₀ hN]
  linarith [hsum]

/-- Entropy is capped by the log of the size of the underlying set. -/
theorem uEnt_le_logb_card (s : Finset α) (g : α → β) :
    uEnt s g ≤ Real.logb 2 s.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, (0 : ℝ) ≤ Real.logb 2 (#{x ∈ s | g x = g a} : ℝ) := by
    intro a ha
    have : (1 : ℝ) ≤ (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    exact Real.logb_nonneg (by norm_num) this
  have : (0 : ℝ) ≤ ∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ) :=
    Finset.sum_nonneg hterm
  have : (0 : ℝ) ≤ (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)) / s.card :=
    div_nonneg this (le_of_lt hN)
  simp only [uEnt]
  linarith

/-- **Data processing for deterministic read-outs.** Coarsening a random variable
by post-composing with any map can only lose information: `H(h ∘ g) ≤ H(g)`. -/
theorem uEnt_comp_le [DecidableEq γ] (s : Finset α) (g : α → β) (h : β → γ) :
    uEnt s (h ∘ g) ≤ uEnt s g := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)
      ≤ Real.logb 2 (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ) := by
    intro a ha
    have hsub : {x ∈ s | g x = g a} ⊆ {x ∈ s | (h ∘ g) x = (h ∘ g) a} := by
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, by simp [Function.comp, hx.2]⟩
    have hc : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    have hle : (#{x ∈ s | g x = g a} : ℝ) ≤ (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact Real.logb_le_logb_of_le (by norm_num) hc hle
  have hsum := Finset.sum_le_sum hterm
  have hdiv : (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)) / s.card
      ≤ (∑ a ∈ s, Real.logb 2 (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ)) / s.card := by
    gcongr
  simp only [uEnt]
  linarith

/-- A set with at most one element carries no entropy. -/
lemma uEnt_of_card_le_one (h : s.card ≤ 1) (g : α → β) : uEnt s g = 0 := by
  classical
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · rw [Finset.card_eq_zero] at h0
    simp [uEnt, h0]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp [uEnt, Finset.filter_singleton]

/-- The count-form of the entropy, the engine of every exact evaluation below:
if the multiset of fibre cardinalities of `g` is `cs`, then
`H(g) = log₂ |s| - (1/|s|) ∑_{c ∈ cs} c log₂ c`. -/
lemma sum_logb_fiber (s : Finset α) (g : α → β) :
    ∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)
      = ∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
  rw [Finset.sum_comp (fun v : β => Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) g]
  simp [nsmul_eq_mul]

lemma uEnt_eq_countSum (s : Finset α) (g : α → β) (cs : Multiset ℕ)
    (h : (s.image g).val.map (fun v => (#{x ∈ s | g x = v} : ℕ)) = cs) :
    uEnt s g = Real.logb 2 s.card
      - (cs.map (fun c : ℕ => (c : ℝ) * Real.logb 2 (c : ℝ))).sum / s.card := by
  rw [uEnt, sum_logb_fiber, ← h, Finset.sum, Multiset.map_map]
  rfl

/-- If the conditioning variable `k` separates the points of `s`, the conditional
entropy vanishes: knowing `k` pins down everything. -/
lemma condEnt_eq_zero_of_injOn [DecidableEq γ] {k : α → γ} (g : α → β)
    (hk : Set.InjOn k s) : condEnt s g k = 0 := by
  classical
  refine Finset.sum_eq_zero fun c hc => ?_
  have hcard : (#{x ∈ s | k x = c}) ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [mem_filter] at hx hy
    exact hk hx.1 hy.1 (by rw [hx.2, hy.2])
  rw [uEnt_of_card_le_one hcard, mul_zero]

end General

/-! ## 2. The splitting type of a cyclic Frobenius -/

-- [dropped: platform already declares ordType]
lemma ordType_zero {n : ℕ} (hn : 0 < n) : ordType n 0 = 1 := by
  simp [ordType, Nat.div_self hn]

/-- **Thickening is free at the level of the type**: the splitting type only
depends on the residue `a mod n`, so refining the residue to a higher modulus
cannot change it. -/
lemma ordType_mod (n a : ℕ) : ordType n (a % n) = ordType n a := by
  rw [ordType, ordType, ← Nat.gcd_rec n a, Nat.gcd_comm]

lemma ordType_dvd {n : ℕ} (a : ℕ) : ordType n a ∣ n :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a n)

/-- **Group-theoretic grounding.** In any finite group, the order of `g ^ a` is
given by the arithmetic function `ordType (orderOf g) a`; for a generator of a
cyclic group of order `n` this is exactly the Frobenius order used above. -/
theorem orderOf_pow_eq_ordType {G : Type*} [Group G] [Finite G] (g : G) (a : ℕ) :
    orderOf (g ^ a) = ordType (orderOf g) a := by
  rw [orderOf_pow, ordType, Nat.gcd_comm]

/-- **The exact type-count law**: for every divisor `d ∣ n` exactly `φ d` of the
`n` residues have splitting type `d`. (This is the source of the rates
`{1/4,1/4,1/2}` for `C₄`, `{1/6,1/6,1/3,1/3}` for `C₆`, and so on.) -/
theorem card_ordType_eq_totient {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    #{a ∈ range n | ordType n a = d} = Nat.totient d := by
  obtain ⟨k, hk⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp [hk] at hn)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp [hk] at hn)
  have key : ∀ a, a < n → ordType n a = d → Nat.gcd a n = k := by
    intro a _ hgd
    have h1 : Nat.gcd a n ∣ n := Nat.gcd_dvd_right _ _
    have h2 : Nat.gcd a n * d = n := by rw [← hgd, ordType]; exact Nat.mul_div_cancel' h1
    have : d * Nat.gcd a n = d * k := by rw [Nat.mul_comm] at h2; omega
    exact Nat.eq_of_mul_eq_mul_left hd0 this
  rw [Nat.totient]
  refine (Finset.card_bij' (fun m _ => m * k) (fun a _ => a / k) ?_ ?_ ?_ ?_).symm
  · intro m hm
    simp only [mem_filter, mem_range] at hm ⊢
    have hco : Nat.gcd m d = 1 := Nat.Coprime.symm hm.2
    refine ⟨by calc m * k < d * k := (Nat.mul_lt_mul_right hk0).2 hm.1
              _ = n := hk.symm, ?_⟩
    have hg : Nat.gcd (m * k) n = k := by
      rw [hk, Nat.mul_comm m k, Nat.mul_comm d k, Nat.gcd_mul_left, hco, Nat.mul_one]
    rw [ordType, hg, hk, Nat.mul_div_cancel _ hk0]
  · intro a ha
    simp only [mem_filter, mem_range] at ha ⊢
    have hg : Nat.gcd a n = k := key a ha.1 ha.2
    have hka : k ∣ a := hg ▸ Nat.gcd_dvd_left a n
    obtain ⟨m, rfl⟩ := hka
    rw [Nat.mul_div_cancel_left _ hk0]
    have hco : Nat.gcd m d = 1 := by
      rw [hk, Nat.mul_comm d k, Nat.gcd_mul_left] at hg
      exact Nat.eq_of_mul_eq_mul_left hk0 (by rw [Nat.mul_one]; exact hg)
    refine ⟨?_, Nat.Coprime.symm hco⟩
    have hlt : k * m < d * k := hk ▸ ha.1
    nlinarith [hlt]
  · intro m _
    exact Nat.mul_div_cancel _ hk0
  · intro a ha
    simp only [mem_filter, mem_range] at ha
    have hg : Nat.gcd a n = k := key a ha.1 ha.2
    exact Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left a n)

/-! ## 3. The type channel and the semiprime type-pair channel -/

/-- The residues (exponents) of the two prime factors of a semiprime. -/
-- [dropped: platform already declares box]
-- [dropped: platform already declares typePair]
-- [dropped: platform already declares prodRes]
-- [dropped: platform already declares rootCount]
-- [dropped: platform already declares sProj]
-- [dropped: platform already declares typeEntropy]
-- [dropped: platform already declares pairEntropy]
-- [dropped: platform already declares condPairEntropy]
-- [dropped: platform already declares Ipair]
-- [dropped: platform already declares Isplit]
lemma Ipair_eq (n : ℕ) : Ipair n = pairEntropy n - condPairEntropy n := rfl

lemma Isplit_eq (n : ℕ) :
    Isplit n = uEnt (box n) (sProj ∘ typePair n)
      - condEnt (box n) (sProj ∘ typePair n) (prodRes n) := rfl

/-- **The which-factor wall.** The type pair is a symmetric function of the two
primes, so it cannot distinguish `p` from `q`. -/
theorem typePair_symm (n : ℕ) (a b : ℕ) : typePair n (a, b) = typePair n (b, a) := by
  simp [typePair, min_comm, max_comm]

/-- The residue of the product is symmetric too. -/
theorem prodRes_symm (n : ℕ) (a b : ℕ) : prodRes n (a, b) = prodRes n (b, a) := by
  simp [prodRes, Nat.add_comm]

/-- **The residue determines the type exactly**: `I(p mod f ; T) = H(T)`. -/
theorem mutInfo_residue_type (n : ℕ) : mutInfo (range n) (ordType n) id = typeEntropy n := by
  rw [mutInfo, condEnt_eq_zero_of_injOn _ (Set.injOn_id _), sub_zero, typeEntropy]

/-- **Thickening zero.** Refining the residue `p mod f` to any finer invariant
`w` (for instance `p mod f²`) leaves the type channel unchanged: it is already
exactly `H(T)`. -/
theorem thickening_zero {γ : Type*} [DecidableEq γ] (n : ℕ) (w : ℕ → γ)
    (hw : Set.InjOn w (range n)) : mutInfo (range n) (ordType n) w = typeEntropy n := by
  rw [mutInfo, condEnt_eq_zero_of_injOn _ hw, sub_zero, typeEntropy]

/-- **The root-count read-out is a coarsening of the type**, hence (data
processing) can never carry more information than the type itself. -/
theorem rootCount_entropy_le (n : ℕ) :
    uEnt (range n) (rootCount n ∘ ordType n) ≤ typeEntropy n :=
  uEnt_comp_le _ _ _

/-- **The `s`-projection is a coarsening of the type pair.** -/
theorem sProj_entropy_le (n : ℕ) :
    uEnt (box n) (sProj ∘ typePair n) ≤ pairEntropy n :=
  uEnt_comp_le _ _ _

/-- Conditioning does not disturb the coarsening order. -/
theorem condEnt_comp_le {β' γ : Type*} [DecidableEq β] [DecidableEq β'] [DecidableEq γ]
    (s : Finset α) (g : α → β) (h : β → β') (k : α → γ) :
    condEnt s (h ∘ g) k ≤ condEnt s g k := by
  refine Finset.sum_le_sum fun c _ => ?_
  have := uEnt_comp_le {x ∈ s | k x = c} g h
  have hw : (0 : ℝ) ≤ (#{x ∈ s | k x = c} : ℝ) / s.card := by positivity
  exact mul_le_mul_of_nonneg_left this hw

/-! ## 4. Base-two logarithms of the numerals that occur -/

lemma lb_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow]; simp

lemma lb_4 : Real.logb 2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_8 : Real.logb 2 (8 : ℝ) = 3 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_16 : Real.logb 2 (16 : ℝ) = 4 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_32 : Real.logb 2 (32 : ℝ) = 5 := by
  rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_64 : Real.logb 2 (64 : ℝ) = 6 := by
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_256 : Real.logb 2 (256 : ℝ) = 8 := by
  rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, lb_pow]; norm_num

lemma lb_6 : Real.logb 2 (6 : ℝ) = 1 + Real.logb 2 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num)]
  simp

lemma lb_12 : Real.logb 2 (12 : ℝ) = 2 + Real.logb 2 3 := by
  rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num), lb_4]

lemma lb_36 : Real.logb 2 (36 : ℝ) = 2 + 2 * Real.logb 2 3 := by
  rw [show (36 : ℝ) = 4 * (3 * 3) by norm_num, Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_mul (by norm_num) (by norm_num), lb_4]
  ring

lemma lb_144 : Real.logb 2 (144 : ℝ) = 4 + 2 * Real.logb 2 3 := by
  rw [show (144 : ℝ) = 16 * (3 * 3) by norm_num, Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_mul (by norm_num) (by norm_num), lb_16]
  ring

lemma lb_9 : Real.logb 2 (9 : ℝ) = 2 * Real.logb 2 3 := by
  rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.logb_pow]
  norm_num

lemma lb_25 : Real.logb 2 (25 : ℝ) = 2 * Real.logb 2 5 := by
  rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.logb_pow]
  norm_num

lemma lb_81 : Real.logb 2 (81 : ℝ) = 4 * Real.logb 2 3 := by
  rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, Real.logb_pow]
  norm_num

lemma lb_15 : Real.logb 2 (15 : ℝ) = Real.logb 2 3 + Real.logb 2 5 := by
  rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.logb_mul (by norm_num) (by norm_num)]

lemma lb_24 : Real.logb 2 (24 : ℝ) = 3 + Real.logb 2 3 := by
  rw [show (24 : ℝ) = 8 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num), lb_8]

lemma lb_225 : Real.logb 2 (225 : ℝ) = 2 * Real.logb 2 3 + 2 * Real.logb 2 5 := by
  rw [show (225 : ℝ) = 9 * 25 by norm_num, Real.logb_mul (by norm_num) (by norm_num), lb_9,
    lb_25]

lemma lb_10 : Real.logb 2 (10 : ℝ) = 1 + Real.logb 2 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.logb_mul (by norm_num) (by norm_num)]
  simp

lemma lb_100 : Real.logb 2 (100 : ℝ) = 2 + 2 * Real.logb 2 5 := by
  rw [show (100 : ℝ) = 4 * (5 * 5) by norm_num, Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_mul (by norm_num) (by norm_num), lb_4]
  ring

/-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/

/-- The splitting types occurring in the `C n` channel are exactly the divisors of `n`. -/
theorem image_ordType (n : ℕ) (hn : 0 < n) : (range n).image (ordType n) = n.divisors := by
  ext d
  simp only [mem_image, mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨a, _, rfl⟩
    exact ⟨ordType_dvd a, hn.ne'⟩
  · rintro ⟨hd, -⟩
    refine ⟨(n / d) % n, Nat.mod_lt _ hn, ?_⟩
    rw [ordType_mod, ordType, Nat.gcd_eq_left (Nat.div_dvd_of_dvd hd),
      Nat.div_div_self hd hn.ne']

/-- **The exact `φ`-law for the type channel.** For every `n > 0`,
`H(T) = ∑_{d ∣ n} (φ(d)/n) · log₂ (n / φ(d))`;
the splitting type `d` occurs with rate `φ(d)/n`. -/
theorem typeEntropy_formula (n : ℕ) (hn : 0 < n) :
    typeEntropy n
      = ∑ d ∈ n.divisors, ((Nat.totient d : ℝ) / n) * Real.logb 2 ((n : ℝ) / Nat.totient d) := by
  have hne : (range n).Nonempty := by
    exact ⟨0, mem_range.2 hn⟩
  rw [typeEntropy, uEnt_eq_shannon hne, image_ordType n hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ∣ n := (Nat.mem_divisors.1 hd).1
  have hcard : (#{x ∈ range n | ordType n x = d}) = Nat.totient d :=
    card_ordType_eq_totient hn hd'
  have hphi : (0 : ℝ) < (Nat.totient d : ℝ) := by
    have : 0 < Nat.totient d := Nat.totient_pos.2 (Nat.pos_of_dvd_of_pos hd' hn)
    exact_mod_cast this
  have hN : (0 : ℝ) < (#(range n) : ℝ) := by
    simpa using (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))
  rw [hcard, card_range, Real.logb_div (ne_of_gt hphi) (ne_of_gt (by exact_mod_cast hn)),
    Real.logb_div (by exact_mod_cast hn.ne') (ne_of_gt hphi)]
  ring

/-- **The exponent model is faithful.** For a prime `f`, every unit of `ZMod f` is
a power `g ^ a` of a fixed generator with `a < f - 1`, and its Frobenius order —
the residue degree of the corresponding prime in `Q(ζ_f)` — is exactly
`ordType (f - 1) a`. -/
theorem exists_generator_ordType (f : ℕ) [hf : Fact f.Prime] :
    ∃ g : (ZMod f)ˣ, orderOf g = f - 1 ∧
      ∀ u : (ZMod f)ˣ, ∃ a < f - 1, u = g ^ a ∧ orderOf u = ordType (f - 1) a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod f)ˣ)
  have hcard : Nat.card ((ZMod f)ˣ) = f - 1 := by
    have : Fintype.card ((ZMod f)ˣ) = f - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hf.out]
    simpa [Nat.card_eq_fintype_card] using this
  have hord : orderOf g = f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hpos : 0 < f - 1 := by
    have := hf.out.two_le
    omega
  refine ⟨g, hord, fun u => ?_⟩
  have hk' : ∃ k : ℕ, g ^ k = u := by
    have := (mem_powers_iff_mem_zpowers (x := g) (y := u)).2 (hg u)
    exact this
  obtain ⟨k, rfl⟩ := hk'
  refine ⟨k % (f - 1), Nat.mod_lt _ hpos, ?_, ?_⟩
  · rw [← hord, pow_mod_orderOf]
  · rw [orderOf_pow_eq_ordType, hord, ← hord, ordType_mod]

/-- `log₂ 3 > 3/2`, i.e. `9 > 8`. -/
lemma lb_three_gt : (3 : ℝ) / 2 < Real.logb 2 3 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num,
    Real.log_pow, Real.log_pow] at h
  rw [Real.logb, lt_div_iff₀ h2]
  push_cast at h
  linarith

/-- `log₂ 5 > 58/25`, i.e. `5 ^ 25 > 2 ^ 58`. -/
lemma lb_five_gt : (58 : ℝ) / 25 < Real.logb 2 5 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log ((2 : ℝ) ^ (58 : ℕ)) < Real.log ((5 : ℝ) ^ (25 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [Real.logb, lt_div_iff₀ h2]
  push_cast at h
  linarith

/-- `log₂ 3 < 8/5`, i.e. `3 ^ 5 = 243 < 256 = 2 ^ 8`. -/
lemma lb_three_lt : Real.logb 2 3 < (8 : ℝ) / 5 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log ((3 : ℝ) ^ (5 : ℕ)) < Real.log ((2 : ℝ) ^ (8 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [Real.logb, div_lt_iff₀ h2]
  push_cast at h
  linarith

/-- `log₂ 5 < 7/3`, i.e. `5 ^ 3 = 125 < 128 = 2 ^ 7`. -/
lemma lb_five_lt : Real.logb 2 5 < (7 : ℝ) / 3 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log ((5 : ℝ) ^ (3 : ℕ)) < Real.log ((2 : ℝ) ^ (7 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [Real.logb, div_lt_iff₀ h2]
  push_cast at h
  linarith

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannelValues.lean ====
/-
# Exact values of the cyclic splitting-type channel

Exact, closed-form evaluations of the type channel `H(T)`, the semiprime
type-pair entropy `H(Π)`, the conditional entropy `H(Π | N mod f)` and the
type-pair channel `I_pair = H(Π) - (1/φ(f)) ∑_c H(Π_c)` for the cyclic groups
`C₂, C₄, C₆, C₁₀, C₁₂, C₁₆`, i.e. for the cyclotomic fields
`Q(ζ₃), Q(ζ₅), Q(ζ₇), Q(ζ₁₁), Q(ζ₁₃), Q(ζ₁₇)`.

Every value is obtained from the count form `uEnt_eq_countSum` of the entropy
together with a kernel-checked enumeration of the fibre cardinalities over the
unit group.
-/

namespace CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The `C2` channel: `Q(ζ_3)` -/

/-- Exact type entropy of the `C2` channel. -/
theorem typeEntropy_val_2 : typeEntropy 2 = (1 : ℝ) := by
  have h : ((range 2).image (ordType 2)).val.map
      (fun v => (#{x ∈ range 2 | ordType 2 x = v} : ℕ)) = (↑[1, 1] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 2).card = 2 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact entropy of the unordered type pair of a `C2` semiprime. -/
theorem pairEntropy_val_2 : pairEntropy 2 = (3/2 : ℝ) := by
  have h : ((box 2).image (typePair 2)).val.map
      (fun v => (#{q ∈ box 2 | typePair 2 q = v} : ℕ)) = (↑[1, 1, 2] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 2).card = 4 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_2 : condPairEntropy 2 = (1/2 : ℝ) := by
  have himg : (box 2).image (prodRes 2) = range 2 := by decide
  have e0 : uEnt {x ∈ box 2 | prodRes 2 x = 0} (typePair 2) = (1 : ℝ) := by
    have h : (({x ∈ box 2 | prodRes 2 x = 0}).image (typePair 2)).val.map
        (fun v => (#{q ∈ {x ∈ box 2 | prodRes 2 x = 0} | typePair 2 q = v} : ℕ))
        = (↑[1, 1] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 2 | prodRes 2 x = 0}) = 2 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e1 : uEnt {x ∈ box 2 | prodRes 2 x = 1} (typePair 2) = (0 : ℝ) := by
    have h : (({x ∈ box 2 | prodRes 2 x = 1}).image (typePair 2)).val.map
        (fun v => (#{q ∈ {x ∈ box 2 | prodRes 2 x = 1} | typePair 2 q = v} : ℕ))
        = (↑[2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 2 | prodRes 2 x = 1}) = 2 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 2).card = 4 from by decide,
    show (#{x ∈ box 2 | prodRes 2 x = 0}) = 2 from by decide,
    show (#{x ∈ box 2 | prodRes 2 x = 1}) = 2 from by decide]

/-- **The `C2` type-pair channel.** -/
theorem Ipair_val_2 : Ipair 2 = (1 : ℝ) := by
  rw [Ipair_eq, pairEntropy_val_2, condPairEntropy_val_2]
  ring

/-! ### The `C4` channel: `Q(ζ_5)` -/

/-- Exact type entropy of the `C4` channel. -/
theorem typeEntropy_val_4 : typeEntropy 4 = (3/2 : ℝ) := by
  have h : ((range 4).image (ordType 4)).val.map
      (fun v => (#{x ∈ range 4 | ordType 4 x = v} : ℕ)) = (↑[1, 1, 2] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 4).card = 4 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact entropy of the unordered type pair of a `C4` semiprime. -/
theorem pairEntropy_val_4 : pairEntropy 4 = (19/8 : ℝ) := by
  have h : ((box 4).image (typePair 4)).val.map
      (fun v => (#{q ∈ box 4 | typePair 4 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 4).card = 16 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_4 : condPairEntropy 4 = (9/8 : ℝ) := by
  have himg : (box 4).image (prodRes 4) = range 4 := by decide
  have e0 : uEnt {x ∈ box 4 | prodRes 4 x = 0} (typePair 4) = (3/2 : ℝ) := by
    have h : (({x ∈ box 4 | prodRes 4 x = 0}).image (typePair 4)).val.map
        (fun v => (#{q ∈ {x ∈ box 4 | prodRes 4 x = 0} | typePair 4 q = v} : ℕ))
        = (↑[1, 1, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 4 | prodRes 4 x = 0}) = 4 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e1 : uEnt {x ∈ box 4 | prodRes 4 x = 1} (typePair 4) = (1 : ℝ) := by
    have h : (({x ∈ box 4 | prodRes 4 x = 1}).image (typePair 4)).val.map
        (fun v => (#{q ∈ {x ∈ box 4 | prodRes 4 x = 1} | typePair 4 q = v} : ℕ))
        = (↑[2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 4 | prodRes 4 x = 1}) = 4 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e2 : uEnt {x ∈ box 4 | prodRes 4 x = 2} (typePair 4) = (1 : ℝ) := by
    have h : (({x ∈ box 4 | prodRes 4 x = 2}).image (typePair 4)).val.map
        (fun v => (#{q ∈ {x ∈ box 4 | prodRes 4 x = 2} | typePair 4 q = v} : ℕ))
        = (↑[2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 4 | prodRes 4 x = 2}) = 4 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e3 : uEnt {x ∈ box 4 | prodRes 4 x = 3} (typePair 4) = (1 : ℝ) := by
    have h : (({x ∈ box 4 | prodRes 4 x = 3}).image (typePair 4)).val.map
        (fun v => (#{q ∈ {x ∈ box 4 | prodRes 4 x = 3} | typePair 4 q = v} : ℕ))
        = (↑[2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 4 | prodRes 4 x = 3}) = 4 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 4).card = 16 from by decide,
    show (#{x ∈ box 4 | prodRes 4 x = 0}) = 4 from by decide,
    show (#{x ∈ box 4 | prodRes 4 x = 1}) = 4 from by decide,
    show (#{x ∈ box 4 | prodRes 4 x = 2}) = 4 from by decide,
    show (#{x ∈ box 4 | prodRes 4 x = 3}) = 4 from by decide]

/-- **The `C4` type-pair channel.** -/
theorem Ipair_val_4 : Ipair 4 = (5/4 : ℝ) := by
  rw [Ipair_eq, pairEntropy_val_4, condPairEntropy_val_4]
  ring

/-! ### The `C6` channel: `Q(ζ_7)` -/

/-- Exact type entropy of the `C6` channel. -/
theorem typeEntropy_val_6 : typeEntropy 6 = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have h : ((range 6).image (ordType 6)).val.map
      (fun v => (#{x ∈ range 6 | ordType 6 x = v} : ℕ)) = (↑[1, 1, 2, 2] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 6).card = 6 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C6` semiprime. -/
theorem pairEntropy_val_6 : pairEntropy 6 = (-1/18 : ℝ) + (2 : ℝ) * Real.logb 2 3 := by
  have h : ((box 6).image (typePair 6)).val.map
      (fun v => (#{q ∈ box 6 | typePair 6 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4, 4, 4, 4, 8] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 6).card = 36 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_6 : condPairEntropy 6 = (1/18 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have himg : (box 6).image (prodRes 6) = range 6 := by decide
  have e0 : uEnt {x ∈ box 6 | prodRes 6 x = 0} (typePair 6) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 0}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 0} | typePair 6 q = v} : ℕ))
        = (↑[1, 1, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 0}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e1 : uEnt {x ∈ box 6 | prodRes 6 x = 1} (typePair 6) = (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 1}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 1} | typePair 6 q = v} : ℕ))
        = (↑[2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 1}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e2 : uEnt {x ∈ box 6 | prodRes 6 x = 2} (typePair 6) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 2}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 2} | typePair 6 q = v} : ℕ))
        = (↑[1, 1, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 2}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e3 : uEnt {x ∈ box 6 | prodRes 6 x = 3} (typePair 6) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 3}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 3} | typePair 6 q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 3}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e4 : uEnt {x ∈ box 6 | prodRes 6 x = 4} (typePair 6) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 4}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 4} | typePair 6 q = v} : ℕ))
        = (↑[1, 1, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 4}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e5 : uEnt {x ∈ box 6 | prodRes 6 x = 5} (typePair 6) = (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 6 | prodRes 6 x = 5}).image (typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ box 6 | prodRes 6 x = 5} | typePair 6 q = v} : ℕ))
        = (↑[2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 6 | prodRes 6 x = 5}) = 6 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 6).card = 36 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 0}) = 6 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 1}) = 6 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 2}) = 6 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 3}) = 6 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 4}) = 6 from by decide,
    show (#{x ∈ box 6 | prodRes 6 x = 5}) = 6 from by decide]
  ring

/-- **The `C6` type-pair channel.** -/
theorem Ipair_val_6 : Ipair 6 = (-1/9 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  rw [Ipair_eq, pairEntropy_val_6, condPairEntropy_val_6]
  ring

/-! ### The `C10` channel: `Q(ζ_11)` -/

/-- Exact type entropy of the `C10` channel. -/
theorem typeEntropy_val_10 : typeEntropy 10 = (-3/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
  have h : ((range 10).image (ordType 10)).val.map
      (fun v => (#{x ∈ range 10 | ordType 10 x = v} : ℕ)) = (↑[1, 1, 4, 4] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 10).card = 10 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C10` semiprime. -/
theorem pairEntropy_val_10 : pairEntropy 10 = (-93/50 : ℝ) + (2 : ℝ) * Real.logb 2 5 := by
  have h : ((box 10).image (typePair 10)).val.map
      (fun v => (#{q ∈ box 10 | typePair 10 q = v} : ℕ)) = (↑[1, 1, 2, 8, 8, 8, 8, 16, 16, 32] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 10).card = 100 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_10 : condPairEntropy 10 = (1/50 : ℝ) + (-12/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have himg : (box 10).image (prodRes 10) = range 10 := by decide
  have e0 : uEnt {x ∈ box 10 | prodRes 10 x = 0} (typePair 10) = (-3/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 0}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 0} | typePair 10 q = v} : ℕ))
        = (↑[1, 1, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 0}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e1 : uEnt {x ∈ box 10 | prodRes 10 x = 1} (typePair 10) = (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 1}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 1} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 1}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e2 : uEnt {x ∈ box 10 | prodRes 10 x = 2} (typePair 10) = (3/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 2}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 2} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 3, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 2}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e3 : uEnt {x ∈ box 10 | prodRes 10 x = 3} (typePair 10) = (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 3}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 3} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 3}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e4 : uEnt {x ∈ box 10 | prodRes 10 x = 4} (typePair 10) = (3/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 4}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 4} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 3, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 4}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e5 : uEnt {x ∈ box 10 | prodRes 10 x = 5} (typePair 10) = (-8/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 5}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 5} | typePair 10 q = v} : ℕ))
        = (↑[2, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 5}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e6 : uEnt {x ∈ box 10 | prodRes 10 x = 6} (typePair 10) = (3/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 6}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 6} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 3, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 6}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e7 : uEnt {x ∈ box 10 | prodRes 10 x = 7} (typePair 10) = (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 7}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 7} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 7}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e8 : uEnt {x ∈ box 10 | prodRes 10 x = 8} (typePair 10) = (3/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 8}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 8} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 3, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 8}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e9 : uEnt {x ∈ box 10 | prodRes 10 x = 9} (typePair 10) = (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 10 | prodRes 10 x = 9}).image (typePair 10)).val.map
        (fun v => (#{q ∈ {x ∈ box 10 | prodRes 10 x = 9} | typePair 10 q = v} : ℕ))
        = (↑[2, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 10 | prodRes 10 x = 9}) = 10 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 10).card = 100 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 0}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 1}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 2}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 3}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 4}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 5}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 6}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 7}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 8}) = 10 from by decide,
    show (#{x ∈ box 10 | prodRes 10 x = 9}) = 10 from by decide]
  ring

/-- **The `C10` type-pair channel.** -/
theorem Ipair_val_10 : Ipair 10 = (-47/25 : ℝ) + (12/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  rw [Ipair_eq, pairEntropy_val_10, condPairEntropy_val_10]
  ring

/-! ### The `C12` channel: `Q(ζ_13)` -/

/-- Exact type entropy of the `C12` channel. -/
theorem typeEntropy_val_12 : typeEntropy 12 = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have h : ((range 12).image (ordType 12)).val.map
      (fun v => (#{x ∈ range 12 | ordType 12 x = v} : ℕ)) = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 12).card = 12 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C12` semiprime. -/
theorem pairEntropy_val_12 : pairEntropy 12 = (7/8 : ℝ) + (2 : ℝ) * Real.logb 2 3 := by
  have h : ((box 12).image (typePair 12)).val.map
      (fun v => (#{q ∈ box 12 | typePair 12 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 16, 16, 16, 16] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 12).card = 144 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_12 : condPairEntropy 12 = (53/72 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have himg : (box 12).image (prodRes 12) = range 12 := by decide
  have e0 : uEnt {x ∈ box 12 | prodRes 12 x = 0} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 0}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 0} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 0}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e1 : uEnt {x ∈ box 12 | prodRes 12 x = 1} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 1}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 1} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 1}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e2 : uEnt {x ∈ box 12 | prodRes 12 x = 2} (typePair 12) = (2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 2}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 2} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 2}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e3 : uEnt {x ∈ box 12 | prodRes 12 x = 3} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 3}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 3} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 3}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e4 : uEnt {x ∈ box 12 | prodRes 12 x = 4} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 4}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 4} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 4}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e5 : uEnt {x ∈ box 12 | prodRes 12 x = 5} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 5}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 5} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 5}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e6 : uEnt {x ∈ box 12 | prodRes 12 x = 6} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 6}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 6} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 6}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e7 : uEnt {x ∈ box 12 | prodRes 12 x = 7} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 7}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 7} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 7}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e8 : uEnt {x ∈ box 12 | prodRes 12 x = 8} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 8}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 8} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 8}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e9 : uEnt {x ∈ box 12 | prodRes 12 x = 9} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 9}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 9} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 9}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e10 : uEnt {x ∈ box 12 | prodRes 12 x = 10} (typePair 12) = (2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 10}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 10} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 10}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e11 : uEnt {x ∈ box 12 | prodRes 12 x = 11} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 12 | prodRes 12 x = 11}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ box 12 | prodRes 12 x = 11} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 12 | prodRes 12 x = 11}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 12).card = 144 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 0}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 1}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 2}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 3}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 4}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 5}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 6}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 7}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 8}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 9}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 10}) = 12 from by decide,
    show (#{x ∈ box 12 | prodRes 12 x = 11}) = 12 from by decide]
  ring

/-- **The `C12` type-pair channel.** -/
theorem Ipair_val_12 : Ipair 12 = (5/36 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  rw [Ipair_eq, pairEntropy_val_12, condPairEntropy_val_12]
  ring

/-! ### The `C16` channel: `Q(ζ_17)` -/

/-- Exact type entropy of the `C16` channel. -/
theorem typeEntropy_val_16 : typeEntropy 16 = (15/8 : ℝ) := by
  have h : ((range 16).image (ordType 16)).val.map
      (fun v => (#{x ∈ range 16 | ordType 16 x = v} : ℕ)) = (↑[1, 1, 2, 4, 8] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 16).card = 16 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact entropy of the unordered type pair of a `C16` semiprime. -/
theorem pairEntropy_val_16 : pairEntropy 16 = (395/128 : ℝ) := by
  have h : ((box 16).image (typePair 16)).val.map
      (fun v => (#{q ∈ box 16 | typePair 16 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4, 8, 8, 16, 16, 16, 16, 32, 64, 64] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 16).card = 256 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_16 : condPairEntropy 16 = (225/128 : ℝ) := by
  have himg : (box 16).image (prodRes 16) = range 16 := by decide
  have e0 : uEnt {x ∈ box 16 | prodRes 16 x = 0} (typePair 16) = (15/8 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 0}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 0} | typePair 16 q = v} : ℕ))
        = (↑[1, 1, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 0}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e1 : uEnt {x ∈ box 16 | prodRes 16 x = 1} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 1}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 1} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 1}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e2 : uEnt {x ∈ box 16 | prodRes 16 x = 2} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 2}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 2} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 2}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e3 : uEnt {x ∈ box 16 | prodRes 16 x = 3} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 3}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 3} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 3}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e4 : uEnt {x ∈ box 16 | prodRes 16 x = 4} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 4}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 4} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 4}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e5 : uEnt {x ∈ box 16 | prodRes 16 x = 5} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 5}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 5} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 5}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e6 : uEnt {x ∈ box 16 | prodRes 16 x = 6} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 6}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 6} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 6}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e7 : uEnt {x ∈ box 16 | prodRes 16 x = 7} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 7}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 7} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 7}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e8 : uEnt {x ∈ box 16 | prodRes 16 x = 8} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 8}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 8} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 8}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e9 : uEnt {x ∈ box 16 | prodRes 16 x = 9} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 9}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 9} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 9}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e10 : uEnt {x ∈ box 16 | prodRes 16 x = 10} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 10}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 10} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 10}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e11 : uEnt {x ∈ box 16 | prodRes 16 x = 11} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 11}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 11} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 11}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e12 : uEnt {x ∈ box 16 | prodRes 16 x = 12} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 12}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 12} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 12}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e13 : uEnt {x ∈ box 16 | prodRes 16 x = 13} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 13}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 13} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 13}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e14 : uEnt {x ∈ box 16 | prodRes 16 x = 14} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 14}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 14} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 14}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e15 : uEnt {x ∈ box 16 | prodRes 16 x = 15} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ box 16 | prodRes 16 x = 15}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ box 16 | prodRes 16 x = 15} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 16 | prodRes 16 x = 15}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (box 16).card = 256 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 0}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 1}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 2}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 3}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 4}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 5}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 6}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 7}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 8}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 9}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 10}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 11}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 12}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 13}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 14}) = 16 from by decide,
    show (#{x ∈ box 16 | prodRes 16 x = 15}) = 16 from by decide]

/-- **The `C16` type-pair channel.** -/
theorem Ipair_val_16 : Ipair 16 = (85/64 : ℝ) := by
  rw [Ipair_eq, pairEntropy_val_16, condPairEntropy_val_16]
  ring

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannelProduct.lean ====
/-
# Additivity of the counting channel over independent products

The exact values of the cyclic type-pair channel obey an unexpected law:
for coprime cyclic orders the information is *additive*,
`I_pair (m * n) = I_pair m + I_pair n`.

This file proves the structural reason.  In the counting-entropy framework of
`Shared.CyclicTypeChannel` we show that entropy, conditional entropy and mutual
information are **exactly additive over cartesian products** of the underlying
sample sets when both the read-out and the conditioning variable act
coordinatewise.  Together with the transport lemmas (invariance of the channel
under a relabelling of the sample set and under an injective recoding of the
read-out) this turns the Chinese Remainder Theorem into an additivity law for
the splitting-type channel.
-/

namespace CyclicTypeChannel

open Finset

variable {α α' β β' γ γ' : Type*}

/-! ## 1. Fibres of a coordinatewise read-out -/

section Product

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

/-- The fibre of a coordinatewise read-out over a product set is the product of
the two fibres. -/
lemma filter_prod_eq [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (v₁ : β₁) (v₂ : β₂) :
    {x ∈ s₁ ×ˢ s₂ | (g₁ x.1, g₂ x.2) = (v₁, v₂)}
      = {x ∈ s₁ | g₁ x = v₁} ×ˢ {x ∈ s₂ | g₂ x = v₂} := by
  ext ⟨u, v⟩
  simp only [mem_filter, mem_product, Prod.mk.injEq]
  tauto

lemma card_filter_prod [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (v₁ : β₁) (v₂ : β₂) :
    (#{x ∈ s₁ ×ˢ s₂ | (g₁ x.1, g₂ x.2) = (v₁, v₂)})
      = (#{x ∈ s₁ | g₁ x = v₁}) * (#{x ∈ s₂ | g₂ x = v₂}) := by
  rw [filter_prod_eq, card_product]

/-- **Additivity of entropy over independent products.** -/
theorem uEnt_prod [DecidableEq β₁] [DecidableEq β₂] {s₁ : Finset α₁} {s₂ : Finset α₂}
    (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
    uEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) = uEnt s₁ g₁ + uEnt s₂ g₂ := by
  classical
  have hc₁ : (0 : ℝ) < s₁.card := by exact_mod_cast card_pos.2 h₁
  have hc₂ : (0 : ℝ) < s₂.card := by exact_mod_cast card_pos.2 h₂
  have hsum : ∑ x ∈ s₁ ×ˢ s₂,
        Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ x.1, g₂ x.2)} : ℝ)
      = (s₂.card : ℝ) * (∑ a ∈ s₁, Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ))
        + (s₁.card : ℝ) * (∑ b ∈ s₂, Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ)) := by
    rw [Finset.sum_product]
    have hterm : ∀ a ∈ s₁, ∑ b ∈ s₂,
        Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℝ)
        = (s₂.card : ℝ) * Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ)
          + ∑ b ∈ s₂, Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
      intro a ha
      have : ∀ b ∈ s₂,
          Real.logb 2 (#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℝ)
          = Real.logb 2 (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ)
            + Real.logb 2 (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
        intro b hb
        have hp₁ : (0 : ℝ) < (#{x ∈ s₁ | g₁ x = g₁ a} : ℝ) := by
          exact_mod_cast fiber_card_pos ha
        have hp₂ : (0 : ℝ) < (#{x ∈ s₂ | g₂ x = g₂ b} : ℝ) := by
          exact_mod_cast fiber_card_pos hb
        rw [show ((#{y ∈ s₁ ×ˢ s₂ | (g₁ y.1, g₂ y.2) = (g₁ a, g₂ b)} : ℕ) : ℝ)
            = ((#{x ∈ s₁ | g₁ x = g₁ a} : ℕ) : ℝ) * ((#{x ∈ s₂ | g₂ x = g₂ b} : ℕ) : ℝ) from by
          exact_mod_cast congrArg (Nat.cast (R := ℝ)) (card_filter_prod s₁ s₂ g₁ g₂ _ _),
          Real.logb_mul (ne_of_gt hp₁) (ne_of_gt hp₂)]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [uEnt, uEnt, uEnt, hsum, card_product]
  push_cast
  rw [Real.logb_mul (ne_of_gt hc₁) (ne_of_gt hc₂)]
  field_simp
  ring

/-- The image of a coordinatewise read-out over a product is the product of the
images. -/
lemma image_prod_eq [DecidableEq β₁] [DecidableEq β₂]
    (s₁ : Finset α₁) (s₂ : Finset α₂) (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) :
    (s₁ ×ˢ s₂).image (fun x => (g₁ x.1, g₂ x.2)) = (s₁.image g₁) ×ˢ (s₂.image g₂) := by
  ext ⟨v₁, v₂⟩
  simp only [mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h1, h2⟩
    exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
  · rintro ⟨⟨a, ha, h1⟩, b, hb, h2⟩
    exact ⟨a, b, ⟨ha, hb⟩, h1, h2⟩

/-- **Additivity of conditional entropy over independent products.** -/
theorem condEnt_prod [DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    condEnt (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = condEnt s₁ g₁ k₁ + condEnt s₂ g₂ k₂ := by
  classical
  have hc₁ : (0 : ℝ) < s₁.card := by exact_mod_cast card_pos.2 h₁
  have hc₂ : (0 : ℝ) < s₂.card := by exact_mod_cast card_pos.2 h₂
  have hmass₁ : ∑ c ∈ s₁.image k₁, ((#{x ∈ s₁ | k₁ x = c} : ℝ) / s₁.card) = 1 := by
    rw [← Finset.sum_div]
    rw [show ∑ c ∈ s₁.image k₁, ((#{x ∈ s₁ | k₁ x = c} : ℕ) : ℝ) = (s₁.card : ℝ) from by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s₁ k₁)]
    exact div_self (ne_of_gt hc₁)
  have hmass₂ : ∑ c ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c} : ℝ) / s₂.card) = 1 := by
    rw [← Finset.sum_div]
    rw [show ∑ c ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c} : ℕ) : ℝ) = (s₂.card : ℝ) from by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s₂ k₂)]
    exact div_self (ne_of_gt hc₂)
  rw [condEnt, image_prod_eq, Finset.sum_product]
  have hterm : ∀ c₁ ∈ s₁.image k₁, ∑ c₂ ∈ s₂.image k₂,
      ((#{x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (c₁, c₂)} : ℝ) / ((s₁ ×ˢ s₂).card)) *
        uEnt {x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (c₁, c₂)} (fun x => (g₁ x.1, g₂ x.2))
      = ((#{x ∈ s₁ | k₁ x = c₁} : ℝ) / s₁.card) * uEnt {x ∈ s₁ | k₁ x = c₁} g₁
        + ((#{x ∈ s₁ | k₁ x = c₁} : ℝ) / s₁.card) * condEnt s₂ g₂ k₂ := by
    intro c₁ hc
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
    have hne₁ : ({x ∈ s₁ | k₁ x = k₁ a}).Nonempty := ⟨a, by simp [ha]⟩
    have hstep : ∀ c₂ ∈ s₂.image k₂,
        ((#{x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (k₁ a, c₂)} : ℝ) / ((s₁ ×ˢ s₂).card)) *
          uEnt {x ∈ s₁ ×ˢ s₂ | (k₁ x.1, k₂ x.2) = (k₁ a, c₂)} (fun x => (g₁ x.1, g₂ x.2))
        = ((#{x ∈ s₁ | k₁ x = k₁ a} : ℝ) / s₁.card) *
            (((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
              (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)) := by
      intro c₂ hc₂'
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hc₂'
      have hne₂ : ({x ∈ s₂ | k₂ x = k₂ b}).Nonempty := ⟨b, by simp [hb]⟩
      rw [filter_prod_eq, uEnt_prod hne₁ hne₂, card_product, card_product]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have : ∑ c₂ ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
        (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)
        = uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + condEnt s₂ g₂ k₂ := by
      rw [condEnt]
      have hexp : ∀ c₂ ∈ s₂.image k₂, ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) *
          (uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁ + uEnt {x ∈ s₂ | k₂ x = c₂} g₂)
          = ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) * uEnt {x ∈ s₁ | k₁ x = k₁ a} g₁
            + ((#{x ∈ s₂ | k₂ x = c₂} : ℝ) / s₂.card) * uEnt {x ∈ s₂ | k₂ x = c₂} g₂ := by
        intro c₂ _; ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.sum_mul, hmass₂, one_mul]
    rw [this]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hmass₁, one_mul]
  simp only [condEnt]

/-- **Additivity of the channel over independent products.**  If the read-out
and the conditioning variable both act coordinatewise on a product sample set,
the mutual information is the sum of the two component informations. -/
theorem mutInfo_prod [DecidableEq β₁] [DecidableEq β₂] [DecidableEq γ₁] [DecidableEq γ₂]
    {s₁ : Finset α₁} {s₂ : Finset α₂} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (g₁ : α₁ → β₁) (g₂ : α₂ → β₂) (k₁ : α₁ → γ₁) (k₂ : α₂ → γ₂) :
    mutInfo (s₁ ×ˢ s₂) (fun x => (g₁ x.1, g₂ x.2)) (fun x => (k₁ x.1, k₂ x.2))
      = mutInfo s₁ g₁ k₁ + mutInfo s₂ g₂ k₂ := by
  rw [mutInfo, mutInfo, mutInfo, uEnt_prod h₁ h₂, condEnt_prod h₁ h₂]
  ring

end Product

/-! ## 2. Transport: relabelling the sample set and recoding the read-out -/

section Transport

variable [DecidableEq β] [DecidableEq γ]

/-- Entropy only depends on the values the read-out takes on the sample set. -/
theorem uEnt_congr {s : Finset α} {g g' : α → β} (h : ∀ a ∈ s, g a = g' a) :
    uEnt s g = uEnt s g' := by
  have hfil : ∀ a ∈ s, {x ∈ s | g x = g a} = {x ∈ s | g' x = g' a} := by
    intro a ha
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, hgx⟩; exact ⟨hx, by rw [← h x hx, ← h a ha, hgx]⟩
    · rintro ⟨hx, hgx⟩; exact ⟨hx, by rw [h x hx, h a ha, hgx]⟩
  rw [uEnt, uEnt]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [hfil a ha]

/-- Conditional entropy only depends on the values of the read-out on the
sample set. -/
theorem condEnt_congr {s : Finset α} {g g' : α → β} {k : α → γ} (h : ∀ a ∈ s, g a = g' a) :
    condEnt s g k = condEnt s g' k :=
  Finset.sum_congr rfl fun c _ => by
    rw [uEnt_congr (fun a ha => h a (mem_of_mem_filter a ha))]

/-- Conditional entropy only depends on the values of the conditioning variable
on the sample set. -/
theorem condEnt_congr_cond {s : Finset α} {g : α → β} {k k' : α → γ} (h : ∀ a ∈ s, k a = k' a) :
    condEnt s g k = condEnt s g k' := by
  have himg : s.image k = s.image k' := Finset.image_congr h
  rw [condEnt, condEnt, himg]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : {x ∈ s | k x = c} = {x ∈ s | k' x = c} := by
    apply Finset.filter_congr
    intro x hx
    rw [h x hx]
  rw [this]

/-- The channel only depends on the values of the two variables on the sample
set. -/
theorem mutInfo_congr {s : Finset α} {g g' : α → β} {k k' : α → γ} (h : ∀ a ∈ s, g a = g' a)
    (h' : ∀ a ∈ s, k a = k' a) : mutInfo s g k = mutInfo s g' k' := by
  rw [mutInfo, mutInfo, uEnt_congr h, condEnt_congr h, condEnt_congr_cond h']

/-- Entropy only depends on the read-out through the partition it induces, so an
injective recoding of the values changes nothing. -/
theorem uEnt_comp_injOn [DecidableEq β'] {s : Finset α} {g : α → β} {f : β → β'}
    (hf : Set.InjOn f (g '' s)) : uEnt s (f ∘ g) = uEnt s g := by
  classical
  have hfib : ∀ a ∈ s, {x ∈ s | (f ∘ g) x = (f ∘ g) a} = {x ∈ s | g x = g a} := by
    intro a ha
    ext x
    simp only [mem_filter, Function.comp_apply]
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, hf ⟨x, hx, rfl⟩ ⟨a, ha, rfl⟩ hfx⟩
    · rintro ⟨hx, hgx⟩
      exact ⟨hx, by rw [hgx]⟩
  rw [uEnt, uEnt]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [hfib a ha]

/-- Conditional entropy is unchanged by an injective recoding of the read-out. -/
theorem condEnt_comp_injOn [DecidableEq β'] {s : Finset α} {g : α → β} {k : α → γ} {f : β → β'}
    (hf : Set.InjOn f (g '' s)) : condEnt s (f ∘ g) k = condEnt s g k := by
  classical
  refine Finset.sum_congr rfl fun c _ => ?_
  have hsub : ({x ∈ s | k x = c} : Finset α) ⊆ s := filter_subset _ _
  have : Set.InjOn f (g '' ({x ∈ s | k x = c} : Finset α)) := by
    refine hf.mono ?_
    exact Set.image_mono (by exact_mod_cast hsub)
  rw [uEnt_comp_injOn this]

/-- Conditional entropy is unchanged by an injective recoding of the
conditioning variable. -/
theorem condEnt_cond_injOn [DecidableEq γ'] {s : Finset α} {g : α → β} {k : α → γ} {f : γ → γ'}
    (hf : Set.InjOn f (k '' s)) : condEnt s g (f ∘ k) = condEnt s g k := by
  classical
  rw [condEnt, condEnt, ← Finset.image_image]
  rw [Finset.sum_image (by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
    exact hf ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hxy)]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
  have hfib : {x ∈ s | (f ∘ k) x = f (k a)} = {x ∈ s | k x = k a} := by
    ext x
    simp only [mem_filter, Function.comp_apply]
    exact ⟨fun h => ⟨h.1, hf ⟨x, h.1, rfl⟩ ⟨a, ha, rfl⟩ h.2⟩, fun h => ⟨h.1, by rw [h.2]⟩⟩
  rw [hfib]

/-- The channel is unchanged by injective recodings of either variable. -/
theorem mutInfo_comp_injOn [DecidableEq β'] [DecidableEq γ'] {s : Finset α} {g : α → β}
    {k : α → γ} {f : β → β'} {e : γ → γ'} (hf : Set.InjOn f (g '' s))
    (he : Set.InjOn e (k '' s)) : mutInfo s (f ∘ g) (e ∘ k) = mutInfo s g k := by
  rw [mutInfo, uEnt_comp_injOn hf, condEnt_comp_injOn hf, condEnt_cond_injOn he, mutInfo]

/-- Relabelling the sample set along an injection leaves the entropy unchanged. -/
theorem uEnt_map {s : Finset α} (e : α ↪ α') (g : α' → β) :
    uEnt (s.map e) g = uEnt s (g ∘ e) := by
  classical
  have hfib : ∀ a ∈ s, (#{x ∈ s.map e | g x = g (e a)}) = #{x ∈ s | (g ∘ e) x = (g ∘ e) a} := by
    intro a _
    rw [Finset.filter_map]
    exact Finset.card_map _
  rw [uEnt, uEnt, Finset.card_map]
  congr 1
  congr 1
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h := hfib a ha
  simp only [Function.comp_apply] at h ⊢
  rw [h]

/-- Relabelling the sample set along an injection leaves the conditional entropy
unchanged. -/
theorem condEnt_map {s : Finset α} (e : α ↪ α') (g : α' → β) (k : α' → γ) :
    condEnt (s.map e) g k = condEnt s (g ∘ e) (k ∘ e) := by
  classical
  have himg : (s.map e).image k = s.image (k ∘ e) := by
    ext c
    simp only [mem_image, mem_map, Function.comp_apply]
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨e a, ⟨a, ha, rfl⟩, rfl⟩
  rw [condEnt, condEnt, himg, Finset.card_map]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hfil : {x ∈ s.map e | k x = c} = ({x ∈ s | (k ∘ e) x = c}).map e := by
    rw [Finset.filter_map]
    rfl
  rw [hfil, Finset.card_map, uEnt_map]

/-- The channel is invariant under a relabelling of the sample set. -/
theorem mutInfo_map {s : Finset α} (e : α ↪ α') (g : α' → β) (k : α' → γ) :
    mutInfo (s.map e) g k = mutInfo s (g ∘ e) (k ∘ e) := by
  rw [mutInfo, mutInfo, uEnt_map, condEnt_map]

/-- Entropy is invariant under any relabelling of the sample set which is
injective *on that set*. -/
theorem uEnt_image_injOn [DecidableEq α'] {s : Finset α} {i : α → α'} (hi : Set.InjOn i s)
    (g : α' → β) : uEnt (s.image i) g = uEnt s (g ∘ i) := by
  classical
  have hsub : ∀ (t : Finset α), t ⊆ s → Set.InjOn i t := by
    intro t ht
    exact hi.mono (by exact_mod_cast ht)
  have hfib : ∀ a ∈ s, {x ∈ s.image i | g x = g (i a)}
      = ({x ∈ s | (g ∘ i) x = (g ∘ i) a}).image i := by
    intro a _
    ext y
    simp only [mem_filter, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hgy⟩; exact ⟨x, ⟨hx, hgy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hgx⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hgx⟩
  rw [uEnt, uEnt, Finset.card_image_of_injOn hi]
  congr 1
  congr 1
  rw [Finset.sum_image (fun x hx y hy hxy => hi hx hy hxy)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hfib a ha, Finset.card_image_of_injOn (hsub _ (filter_subset _ _))]

/-- Conditional entropy is invariant under a relabelling of the sample set which
is injective on that set. -/
theorem condEnt_image_injOn [DecidableEq α'] {s : Finset α} {i : α → α'} (hi : Set.InjOn i s)
    (g : α' → β) (k : α' → γ) : condEnt (s.image i) g k = condEnt s (g ∘ i) (k ∘ i) := by
  classical
  have hsub : ∀ (t : Finset α), t ⊆ s → Set.InjOn i t := by
    intro t ht
    exact hi.mono (by exact_mod_cast ht)
  rw [condEnt, condEnt, Finset.image_image, Finset.card_image_of_injOn hi]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hfib : {x ∈ s.image i | k x = c} = ({x ∈ s | (k ∘ i) x = c}).image i := by
    ext y
    simp only [mem_filter, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hky⟩; exact ⟨x, ⟨hx, hky⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hkx⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hkx⟩
  rw [hfib, Finset.card_image_of_injOn (hsub _ (filter_subset _ _)),
    uEnt_image_injOn (hsub _ (filter_subset _ _))]

/-- **The channel is invariant under a relabelling of the sample set.** -/
theorem mutInfo_image_injOn [DecidableEq α'] {s : Finset α} {i : α → α'} (hi : Set.InjOn i s)
    (g : α' → β) (k : α' → γ) : mutInfo (s.image i) g k = mutInfo s (g ∘ i) (k ∘ i) := by
  rw [mutInfo, mutInfo, uEnt_image_injOn hi, condEnt_image_injOn hi]

end Transport

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannelSymmetry.lean ====
/-
# The which-factor wall is exactly zero

A semiprime `N = p q` presents its two prime factors symmetrically: nothing in
`N mod f` can say *which* factor carries which splitting type.  Experimentally
the "which-factor" information was measured at `0.0001` bits, i.e. zero.

This file proves that it is **exactly** zero, in complete generality:  for any
sample set carrying an involution `σ` which swaps the two components of the
read-out and fixes the conditioning variable, forgetting the order of the two
components changes both the entropy and the conditional entropy by *the same*
amount, namely the probability of an off-diagonal pair.  Consequently the
mutual information of the unordered read-out equals that of the ordered one.

The entropies themselves are genuinely different (the ordered pair carries
strictly more entropy whenever off-diagonal pairs occur); it is only the
*channel* that is insensitive to the ordering.
-/

namespace CyclicTypeChannel

open Finset

section Symmetrization

variable {α β : Type*} [LinearOrder β]

/-- Forget the order of an ordered pair. -/
def symPair (z : β × β) : β × β := (min z.1 z.2, max z.1 z.2)

/-- Two ordered pairs have the same unordered shadow exactly when they agree, or
agree after a swap. -/
theorem symPair_eq_iff (z w : β × β) :
    symPair z = symPair w ↔ z = w ∨ z = (w.2, w.1) := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [symPair, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total z1 z2 with hz | hz <;> rcases le_total w1 w2 with hw | hw <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hz, hw] at h1 h2 <;>
      subst h1 <;> subst h2 <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨rfl, rfl⟩
    · exact ⟨min_comm _ _, max_comm _ _⟩

variable [DecidableEq β] {s : Finset α} {g : α → β × β} {σ : α → α}

omit [LinearOrder β] in
/-- The swapped fibre has the same size as the fibre: the involution `σ` maps one
onto the other. -/
theorem card_swap_fiber (hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
    (#{x ∈ s | g x = ((g a).2, (g a).1)}) = #{x ∈ s | g x = g a} := by
  classical
  refine Finset.card_bij' (fun x _ => σ x) (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hσs x hx.1, ?_⟩
    rw [hgσ x hx.1, hx.2]
  · intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hσs x hx.1, ?_⟩
    rw [hgσ x hx.1, hx.2]
  · intro x hx
    exact hσσ x (mem_of_mem_filter x hx)
  · intro x hx
    exact hσσ x (mem_of_mem_filter x hx)

/-- The unordered fibre is the union of the fibre and its swap. -/
theorem card_symPair_fiber (hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) (a : α) :
    (#{x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a})
      = (if (g a).1 = (g a).2 then 1 else 2) * #{x ∈ s | g x = g a} := by
  classical
  have hsplit : {x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a}
      = {x ∈ s | g x = g a} ∪ {x ∈ s | g x = ((g a).2, (g a).1)} := by
    ext x
    simp only [mem_filter, mem_union, Function.comp_apply]
    constructor
    · rintro ⟨hx, hsx⟩
      rcases (symPair_eq_iff _ _).1 hsx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, by rw [h]⟩
      · exact ⟨hx, (symPair_eq_iff _ _).2 (Or.inr h)⟩
  by_cases hd : (g a).1 = (g a).2
  · have heq : {x ∈ s | g x = ((g a).2, (g a).1)} = {x ∈ s | g x = g a} := by
      have : ((g a).2, (g a).1) = g a := Prod.ext_iff.2 ⟨hd.symm, hd⟩
      rw [this]
    rw [hsplit, heq, Finset.union_self, if_pos hd, one_mul]
  · have hdisj : Disjoint ({x ∈ s | g x = g a}) ({x ∈ s | g x = ((g a).2, (g a).1)}) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_filter] at hx hx'
      rw [hx.2] at hx'
      exact hd (congrArg Prod.fst hx'.2)
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      card_swap_fiber hσs hσσ hgσ a, if_neg hd]
    ring

/-- **The entropy defect of forgetting the order.**  Passing from the ordered to
the unordered read-out costs exactly the probability of an off-diagonal pair:
each unordered off-diagonal value merges two equally likely ordered values. -/
theorem uEnt_symPair (hσs : ∀ a ∈ s, σ a ∈ s) (hσσ : ∀ a ∈ s, σ (σ a) = a)
    (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1)) :
    uEnt s (symPair ∘ g) = uEnt s g - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, Real.logb 2 (#{x ∈ s | (symPair ∘ g) x = (symPair ∘ g) a} : ℝ)
      = Real.logb 2 (#{x ∈ s | g x = g a} : ℝ) + (if (g a).1 ≠ (g a).2 then (1 : ℝ) else 0) := by
    intro a ha
    have hpos : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by exact_mod_cast fiber_card_pos ha
    have hcard := card_symPair_fiber hσs hσσ hgσ a
    by_cases hd : (g a).1 = (g a).2
    · rw [hcard, if_pos hd, if_neg (by simpa using hd)]
      simp
    · rw [hcard, if_neg hd, if_pos hd]
      push_cast
      rw [Real.logb_mul (by norm_num) (ne_of_gt hpos),
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      ring
  have hcount : ∑ a ∈ s, (if (g a).1 ≠ (g a).2 then (1 : ℝ) else 0)
      = (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero]
  rw [uEnt, uEnt, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hcount]
  field_simp
  ring

/-- **The conditional entropy defect is the same.**  If the involution also fixes
the conditioning variable, conditioning does not change the cost of forgetting
the order. -/
theorem condEnt_symPair {γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    condEnt s (symPair ∘ g) k = condEnt s g k - (#{a ∈ s | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [condEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ c ∈ s.image k,
      ((#{x ∈ s | k x = c} : ℝ) / s.card) * uEnt {x ∈ s | k x = c} (symPair ∘ g)
      = ((#{x ∈ s | k x = c} : ℝ) / s.card) * uEnt {x ∈ s | k x = c} g
        - (#{a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2} : ℝ) / s.card := by
    intro c hc
    have hne : ({x ∈ s | k x = c}).Nonempty := by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      exact ⟨a, by simp [ha]⟩
    have hNc : (0 : ℝ) < (#{x ∈ s | k x = c} : ℝ) := by exact_mod_cast card_pos.2 hne
    have h1 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), σ a ∈ ({x ∈ s | k x = c} : Finset α) := by
      intro a ha
      simp only [mem_filter] at ha ⊢
      exact ⟨hσs a ha.1, by rw [hkσ a ha.1, ha.2]⟩
    have h2 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), σ (σ a) = a :=
      fun a ha => hσσ a (mem_of_mem_filter a ha)
    have h3 : ∀ a ∈ ({x ∈ s | k x = c} : Finset α), g (σ a) = ((g a).2, (g a).1) :=
      fun a ha => hgσ a (mem_of_mem_filter a ha)
    rw [uEnt_symPair h1 h2 h3]
    field_simp
  rw [condEnt, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← condEnt, ← Finset.sum_div]
  congr 1
  congr 1
  have hfil : ∀ c, {a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2}
      = {x ∈ ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α) | k x = c} := by
    intro c
    ext x
    simp only [mem_filter]
    tauto
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := k) (s := ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α)) (t := s.image k)
    (fun x hx => mem_image_of_mem k (mem_of_mem_filter x hx))
  rw [show ∑ c ∈ s.image k, ((#{a ∈ ({x ∈ s | k x = c} : Finset α) | (g a).1 ≠ (g a).2} : ℕ) : ℝ)
      = ∑ c ∈ s.image k, ((#{x ∈ ({a ∈ s | (g a).1 ≠ (g a).2} : Finset α) | k x = c} : ℕ) : ℝ) from
    Finset.sum_congr rfl fun c _ => by rw [hfil c]]
  exact_mod_cast hfib.symm

/-- **The which-factor wall is exactly zero.**  Forgetting which of the two
components carries which value costs the same entropy with or without knowing
the conditioning variable, so the *channel* is unchanged. -/
theorem mutInfo_symPair {γ : Type*} [DecidableEq γ] {k : α → γ} (hσs : ∀ a ∈ s, σ a ∈ s)
    (hσσ : ∀ a ∈ s, σ (σ a) = a) (hgσ : ∀ a ∈ s, g (σ a) = ((g a).2, (g a).1))
    (hkσ : ∀ a ∈ s, k (σ a) = k a) :
    mutInfo s (symPair ∘ g) k = mutInfo s g k := by
  rw [mutInfo, mutInfo, uEnt_symPair hσs hσσ hgσ, condEnt_symPair hσs hσσ hgσ hkσ]
  ring

end Symmetrization

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannelCRTLaw.lean ====
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `box (m*n)` as
  the product `box m ×ˢ box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/


namespace CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/

/-- The **ordered** splitting-type pair `(T(p), T(q))` of a semiprime `N = p q`. -/
def ordPair (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (ordType n p.1, ordType n p.2)

/-- The ordered type-pair channel `I((T(p),T(q)) ; N mod f)`. -/
noncomputable def IpairOrd (n : ℕ) : ℝ := mutInfo (box n) (ordPair n) (prodRes n)

lemma ordType_pos {n : ℕ} (hn : 0 < n) (a : ℕ) : 0 < ordType n a :=
  Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right a n)) (Nat.gcd_pos_of_pos_right a hn)

/-! ## 2. Multiplicativity of the splitting type -/

/-- **The splitting type is multiplicative in the order.**  For coprime `m, n`
the type of an exponent in `C_{mn}` is the product of its types in `C_m` and
`C_n`; this is the type-level shadow of `C_{mn} ≅ C_m × C_n`. -/
theorem ordType_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    ordType (m * n) a = ordType m a * ordType n a := by
  rw [ordType, ordType, ordType, h.gcd_mul a,
    Nat.div_mul_div_comm (Nat.gcd_dvd_right a m) (Nat.gcd_dvd_right a n)]

/-- Splitting the product of a divisor of `m` with a divisor of `n` back into its
two factors is unambiguous when `m` and `n` are coprime. -/
theorem eq_of_mul_eq_mul_coprime {m n x x' y y' : ℕ} (h : Nat.Coprime m n) (hm : 0 < m)
    (hx : x ∣ m) (hx' : x' ∣ m) (hy : y ∣ n) (hy' : y' ∣ n) (he : x * y = x' * y') :
    x = x' ∧ y = y' := by
  have hxm : Nat.gcd (x * y) m = x := by
    rw [Nat.Coprime.gcd_mul_right_cancel x (Nat.Coprime.coprime_dvd_left hy h.symm)]
    exact Nat.gcd_eq_left hx
  have hxm' : Nat.gcd (x' * y') m = x' := by
    rw [Nat.Coprime.gcd_mul_right_cancel x' (Nat.Coprime.coprime_dvd_left hy' h.symm)]
    exact Nat.gcd_eq_left hx'
  have hxx : x = x' := by rw [← hxm, ← hxm', he]
  refine ⟨hxx, ?_⟩
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hx hm
  subst hxx
  exact Nat.eq_of_mul_eq_mul_left hxpos he

/-! ## 3. The CRT relabelling of the sample set -/

/-- The Chinese Remainder relabelling of a pair of exponents mod `m * n`. -/
def crtMap (m n : ℕ) (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((p.1 % m, p.2 % m), (p.1 % n, p.2 % n))

/-- CRT uniqueness in the form used below. -/
theorem eq_of_mod_eq_mod {m n : ℕ} (h : Nat.Coprime m n) {a b : ℕ} (ha : a < m * n)
    (hb : b < m * n) (h1 : a % m = b % m) (h2 : a % n = b % n) : a = b := by
  have : a ≡ b [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul h).1 ⟨h1, h2⟩
  have := this
  rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem crtMap_injOn {m n : ℕ} (h : Nat.Coprime m n) :
    Set.InjOn (crtMap m n) (box (m * n)) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
  simp only [box, coe_product, Set.mem_prod, mem_coe, mem_range] at hab hab'
  simp only [crtMap, Prod.mk.injEq] at he
  obtain ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩ := he
  rw [Prod.mk.injEq]
  exact ⟨eq_of_mod_eq_mod h hab.1 hab'.1 ha1 ha2, eq_of_mod_eq_mod h hab.2 hab'.2 hb1 hb2⟩

theorem image_crtMap {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    (box (m * n)).image (crtMap m n) = box m ×ˢ box n := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hx
    simp only [box, mem_product, mem_range] at hab ⊢
    exact ⟨⟨Nat.mod_lt _ hm, Nat.mod_lt _ hm⟩, ⟨Nat.mod_lt _ hn, Nat.mod_lt _ hn⟩⟩
  · rw [Finset.card_image_of_injOn (crtMap_injOn h)]
    simp only [box, card_product, card_range]
    exact le_of_eq (by ring)

/-! ## 4. The additivity law -/

/-- **CRT additivity of the splitting-type channel.**  For coprime cyclic orders
the (ordered) type-pair information splits as a sum over the primary components:
`I(m·n) = I(m) + I(n)`.  This is the exact law behind the observed values
`I(6) = I(2)+I(3)`, `I(10) = I(2)+I(5)`, `I(12) = I(4)+I(3)`,
`I(15) = I(3)+I(5)`. -/
theorem IpairOrd_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    IpairOrd (m * n) = IpairOrd m + IpairOrd n := by
  classical
  -- the coordinatewise read-out and conditioning variable on the product
  set G : ((ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ) × (ℕ × ℕ) := fun X => (ordPair m X.1, ordPair n X.2)
    with hG
  set K : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ × ℕ := fun X => (prodRes m X.1, prodRes n X.2) with hK
  -- the multiplicative recoding of a pair of component types
  set f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ × ℕ := fun z => (z.1.1 * z.2.1, z.1.2 * z.2.2) with hf
  -- the residue-splitting recoding of the product residue
  set d : ℕ → ℕ × ℕ := fun z => (z % m, z % n) with hd
  have hbm : (box m).Nonempty := ⟨(0, 0), by simp [box, mem_product, hm]⟩
  have hbn : (box n).Nonempty := ⟨(0, 0), by simp [box, mem_product, hn]⟩
  -- step 1 : the `m*n` read-out is the multiplicative recoding of the CRT read-out
  have hstep1 : ∀ p ∈ box (m * n), ordPair (m * n) p = (f ∘ (G ∘ crtMap m n)) p := by
    intro p _
    simp only [hf, hG, crtMap, Function.comp_apply, ordPair, Prod.mk.injEq]
    constructor
    · rw [ordType_mul_of_coprime h, ordType_mod, ordType_mod]
    · rw [ordType_mul_of_coprime h, ordType_mod, ordType_mod]
  have hstep2 : ∀ p ∈ box (m * n), (d ∘ prodRes (m * n)) p = (K ∘ crtMap m n) p := by
    intro p _
    simp only [hd, hK, crtMap, Function.comp_apply, prodRes, Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mod_of_dvd _ ⟨n, rfl⟩, Nat.add_mod]
    · rw [Nat.mod_mod_of_dvd _ ⟨m, mul_comm m n⟩, Nat.add_mod]
  -- step 3 : the multiplicative recoding is injective on the values that occur
  have hfinj : Set.InjOn f ((G ∘ crtMap m n) '' (box (m * n))) := by
    rintro z hz z' hz' hzz
    obtain ⟨p, -, rfl⟩ := hz
    obtain ⟨p', -, rfl⟩ := hz'
    simp only [hf, hG, crtMap, Function.comp_apply, ordPair, Prod.mk.injEq] at hzz ⊢
    obtain ⟨h1, h2⟩ := hzz
    have e1 := eq_of_mul_eq_mul_coprime h hm (ordType_dvd (n := m) _) (ordType_dvd (n := m) _)
      (ordType_dvd (n := n) _) (ordType_dvd (n := n) _) h1
    have e2 := eq_of_mul_eq_mul_coprime h hm (ordType_dvd (n := m) _) (ordType_dvd (n := m) _)
      (ordType_dvd (n := n) _) (ordType_dvd (n := n) _) h2
    exact ⟨⟨e1.1, e2.1⟩, ⟨e1.2, e2.2⟩⟩
  -- step 4 : the residue-splitting recoding is injective on the residues that occur
  have hdinj : Set.InjOn d (prodRes (m * n) '' (box (m * n))) := by
    rintro z hz z' hz' hzz
    obtain ⟨p, -, rfl⟩ := hz
    obtain ⟨p', -, rfl⟩ := hz'
    have hlt : ∀ q : ℕ × ℕ, prodRes (m * n) q < m * n := fun q =>
      Nat.mod_lt _ (Nat.mul_pos hm hn)
    simp only [hd, Prod.mk.injEq] at hzz
    exact eq_of_mod_eq_mod h (hlt p) (hlt p') hzz.1 hzz.2
  calc IpairOrd (m * n)
      = mutInfo (box (m * n)) (f ∘ (G ∘ crtMap m n)) (prodRes (m * n)) :=
        mutInfo_congr hstep1 (fun _ _ => rfl)
    _ = mutInfo (box (m * n)) (G ∘ crtMap m n) (prodRes (m * n)) := by
        rw [mutInfo, mutInfo, uEnt_comp_injOn hfinj, condEnt_comp_injOn hfinj]
    _ = mutInfo (box (m * n)) (G ∘ crtMap m n) (d ∘ prodRes (m * n)) := by
        rw [mutInfo, mutInfo, condEnt_cond_injOn hdinj]
    _ = mutInfo (box (m * n)) (G ∘ crtMap m n) (K ∘ crtMap m n) :=
        mutInfo_congr (fun _ _ => rfl) hstep2
    _ = mutInfo ((box (m * n)).image (crtMap m n)) G K :=
        (mutInfo_image_injOn (crtMap_injOn h) G K).symm
    _ = mutInfo (box m ×ˢ box n) G K := by rw [image_crtMap hm hn h]
    _ = IpairOrd m + IpairOrd n := by
        rw [hG, hK, mutInfo_prod hbm hbn]
        rfl

/-! ## 5. From the ordered to the unordered pair -/

/-- The unordered type pair is the unordered shadow of the ordered one. -/
theorem typePair_eq_symPair (n : ℕ) (p : ℕ × ℕ) : typePair n p = symPair (ordPair n p) := rfl

/-- **The which-factor wall is exactly zero for the type-pair channel**: the
unordered type pair carries exactly as much information about `N mod f` as the
ordered one, even though it has strictly smaller entropy whenever the two types
can differ. -/
theorem Ipair_eq_IpairOrd (n : ℕ) : Ipair n = IpairOrd n := by
  have hσs : ∀ p ∈ box n, Prod.swap p ∈ box n := by
    intro p hp
    simp only [box, mem_product, mem_range, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  have hσσ : ∀ p ∈ box n, Prod.swap (Prod.swap p) = p := fun p _ => rfl
  have hgσ : ∀ p ∈ box n, ordPair n (Prod.swap p) = ((ordPair n p).2, (ordPair n p).1) :=
    fun p _ => rfl
  have hkσ : ∀ p ∈ box n, prodRes n (Prod.swap p) = prodRes n p := by
    intro p _
    exact prodRes_symm n p.2 p.1
  rw [Ipair, IpairOrd, show typePair n = symPair ∘ ordPair n from rfl]
  exact mutInfo_symPair hσs hσσ hgσ hkσ

/-- **CRT additivity of the (unordered) semiprime type-pair channel.**  This is
the exact law governing the whole growth table: the information of a cyclic
order is the sum of its primary contributions. -/
theorem Ipair_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    Ipair (m * n) = Ipair m + Ipair n := by
  rw [Ipair_eq_IpairOrd, Ipair_eq_IpairOrd, Ipair_eq_IpairOrd, IpairOrd_mul_of_coprime hm hn h]

/-! ## 6. The channel is determined by its prime-power values -/

/-- The trivial cyclic order carries no information. -/
theorem Ipair_one : Ipair 1 = 0 := by
  have hcard : (box 1).card ≤ 1 := by decide
  have hcond : condEnt (box 1) (typePair 1) (prodRes 1) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have : (#{x ∈ box 1 | prodRes 1 x = c}) ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) hcard
    rw [uEnt_of_card_le_one this, mul_zero]
  rw [Ipair, mutInfo, uEnt_of_card_le_one hcard, hcond, sub_zero]

/-- **The type-pair channel is a sum over the primary components.**  Iterating
CRT additivity, the information carried by a cyclic order is the sum of the
informations of its prime-power parts, so the whole growth table is determined
by the prime-power values alone. -/
theorem Ipair_eq_sum_prime_powers {n : ℕ} (hn : n ≠ 0) :
    Ipair n = ∑ p ∈ n.primeFactors, Ipair (p ^ n.factorization p) := by
  have hmul : ∀ (a b : ℕ), Nat.Coprime a b →
      Real.exp (Ipair (a * b)) = Real.exp (Ipair a) * Real.exp (Ipair b) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.coprime_zero_left] at hab
      subst hab
      simp [Ipair_one]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Nat.coprime_zero_right] at hab
      subst hab
      simp [Ipair_one]
    rw [Ipair_mul_of_coprime ha hb hab, Real.exp_add]
  have hone : Real.exp (Ipair 1) = 1 := by rw [Ipair_one, Real.exp_zero]
  have hfac := Nat.multiplicative_factorization (fun m => Real.exp (Ipair m)) hmul hone hn
  rw [Finsupp.prod, Nat.support_factorization] at hfac
  simp only at hfac
  have hsum : ∏ p ∈ n.primeFactors, Real.exp (Ipair (p ^ n.factorization p))
      = Real.exp (∑ p ∈ n.primeFactors, Ipair (p ^ n.factorization p)) :=
    (Real.exp_sum _ _).symm
  rw [hsum] at hfac
  exact Real.exp_injective hfac

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/Shared/CyclicTypeChannelCRT.lean ====
/-
# CRT additivity of the cyclic type-pair channel

This file extends the exact-value catalogue of the cyclic type-pair channel to
the orders `n ∈ {3, 5, 8, 9, 15}` and proves the two structural laws that the
extended table makes visible.

* **CRT additivity.**  For coprime cyclic orders the type-pair information is
  *exactly additive*:
  `Ipair (n₁ * n₂) = Ipair n₁ + Ipair n₂` whenever `gcd n₁ n₂ = 1`
  (verified here for the pairs `(2,3)`, `(2,5)`, `(4,3)`, `(3,5)`).
  This is the information-theoretic shadow of the CRT decomposition of a cyclic
  group into its primary components.

* **Evenness, not compositeness, breaks the one-bit cap.**  The order `8` is a
  further above-cap example (`21/16 > 1`), while *every* odd order computed here
  (`3, 5, 9, 15`) sits strictly *below* one bit.  So the mechanism which pushes
  the multi-state type channel above the binary-fork cap is the presence of the
  order-two element (the quadratic character), amplified by the remaining
  divisor structure.
-/


namespace CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The abstract cyclic order `C3` -/

/-- Exact type entropy of the `C3` channel. -/
theorem typeEntropy_val_3 : typeEntropy 3 = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have h : ((range 3).image (ordType 3)).val.map
      (fun v => (#{x ∈ range 3 | ordType 3 x = v} : ℕ)) = (↑[1, 2] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 3).card = 3 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C3` semiprime. -/
theorem pairEntropy_val_3 : pairEntropy 3 = (-16/9 : ℝ) + (2 : ℝ) * Real.logb 2 3 := by
  have h : ((box 3).image (typePair 3)).val.map
      (fun v => (#{q ∈ box 3 | typePair 3 q = v} : ℕ)) = (↑[1, 4, 4] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 3).card = 9 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_3 : condPairEntropy 3 = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have himg : (box 3).image (prodRes 3) = range 3 := by decide
  have e0 : uEnt {x ∈ box 3 | prodRes 3 x = 0} (typePair 3) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 3 | prodRes 3 x = 0}).image (typePair 3)).val.map
        (fun v => (#{q ∈ {x ∈ box 3 | prodRes 3 x = 0} | typePair 3 q = v} : ℕ))
        = (↑[1, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 3 | prodRes 3 x = 0}) = 3 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e1 : uEnt {x ∈ box 3 | prodRes 3 x = 1} (typePair 3) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 3 | prodRes 3 x = 1}).image (typePair 3)).val.map
        (fun v => (#{q ∈ {x ∈ box 3 | prodRes 3 x = 1} | typePair 3 q = v} : ℕ))
        = (↑[1, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 3 | prodRes 3 x = 1}) = 3 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e2 : uEnt {x ∈ box 3 | prodRes 3 x = 2} (typePair 3) = (-2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 3 | prodRes 3 x = 2}).image (typePair 3)).val.map
        (fun v => (#{q ∈ {x ∈ box 3 | prodRes 3 x = 2} | typePair 3 q = v} : ℕ))
        = (↑[1, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 3 | prodRes 3 x = 2}) = 3 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (box 3).card = 9 from by decide,
    show (#{x ∈ box 3 | prodRes 3 x = 0}) = 3 from by decide,
    show (#{x ∈ box 3 | prodRes 3 x = 1}) = 3 from by decide,
    show (#{x ∈ box 3 | prodRes 3 x = 2}) = 3 from by decide]
  ring

/-- **The `C3` type-pair channel.** -/
theorem Ipair_val_3 : Ipair 3 = (-10/9 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  rw [Ipair_eq, pairEntropy_val_3, condPairEntropy_val_3]
  ring

/-! ### The abstract cyclic order `C5` -/

/-- Exact type entropy of the `C5` channel. -/
theorem typeEntropy_val_5 : typeEntropy 5 = (-8/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
  have h : ((range 5).image (ordType 5)).val.map
      (fun v => (#{x ∈ range 5 | ordType 5 x = v} : ℕ)) = (↑[1, 4] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 5).card = 5 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C5` semiprime. -/
theorem pairEntropy_val_5 : pairEntropy 5 = (-88/25 : ℝ) + (2 : ℝ) * Real.logb 2 5 := by
  have h : ((box 5).image (typePair 5)).val.map
      (fun v => (#{q ∈ box 5 | typePair 5 q = v} : ℕ)) = (↑[1, 8, 16] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 5).card = 25 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_5 : condPairEntropy 5 = (-16/25 : ℝ) + (-12/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have himg : (box 5).image (prodRes 5) = range 5 := by decide
  have e0 : uEnt {x ∈ box 5 | prodRes 5 x = 0} (typePair 5) = (-8/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 5 | prodRes 5 x = 0}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ box 5 | prodRes 5 x = 0} | typePair 5 q = v} : ℕ))
        = (↑[1, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 5 | prodRes 5 x = 0}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e1 : uEnt {x ∈ box 5 | prodRes 5 x = 1} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 5 | prodRes 5 x = 1}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ box 5 | prodRes 5 x = 1} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 5 | prodRes 5 x = 1}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e2 : uEnt {x ∈ box 5 | prodRes 5 x = 2} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 5 | prodRes 5 x = 2}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ box 5 | prodRes 5 x = 2} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 5 | prodRes 5 x = 2}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e3 : uEnt {x ∈ box 5 | prodRes 5 x = 3} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 5 | prodRes 5 x = 3}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ box 5 | prodRes 5 x = 3} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 5 | prodRes 5 x = 3}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e4 : uEnt {x ∈ box 5 | prodRes 5 x = 4} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 5 | prodRes 5 x = 4}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ box 5 | prodRes 5 x = 4} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 5 | prodRes 5 x = 4}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (box 5).card = 25 from by decide,
    show (#{x ∈ box 5 | prodRes 5 x = 0}) = 5 from by decide,
    show (#{x ∈ box 5 | prodRes 5 x = 1}) = 5 from by decide,
    show (#{x ∈ box 5 | prodRes 5 x = 2}) = 5 from by decide,
    show (#{x ∈ box 5 | prodRes 5 x = 3}) = 5 from by decide,
    show (#{x ∈ box 5 | prodRes 5 x = 4}) = 5 from by decide]
  ring

/-- **The `C5` type-pair channel.** -/
theorem Ipair_val_5 : Ipair 5 = (-72/25 : ℝ) + (12/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  rw [Ipair_eq, pairEntropy_val_5, condPairEntropy_val_5]
  ring

/-! ### The abstract cyclic order `C8` -/

/-- Exact type entropy of the `C8` channel. -/
theorem typeEntropy_val_8 : typeEntropy 8 = (7/4 : ℝ) := by
  have h : ((range 8).image (ordType 8)).val.map
      (fun v => (#{x ∈ range 8 | ordType 8 x = v} : ℕ)) = (↑[1, 1, 2, 4] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 8).card = 8 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]

/-- Exact entropy of the unordered type pair of a `C8` semiprime. -/
theorem pairEntropy_val_8 : pairEntropy 8 = (91/32 : ℝ) := by
  have h : ((box 8).image (typePair 8)).val.map
      (fun v => (#{q ∈ box 8 | typePair 8 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4, 8, 8, 16, 16] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 8).card = 64 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_8 : condPairEntropy 8 = (49/32 : ℝ) := by
  have himg : (box 8).image (prodRes 8) = range 8 := by decide
  have e0 : uEnt {x ∈ box 8 | prodRes 8 x = 0} (typePair 8) = (7/4 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 0}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 0} | typePair 8 q = v} : ℕ))
        = (↑[1, 1, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 0}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e1 : uEnt {x ∈ box 8 | prodRes 8 x = 1} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 1}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 1} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 1}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e2 : uEnt {x ∈ box 8 | prodRes 8 x = 2} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 2}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 2} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 2}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e3 : uEnt {x ∈ box 8 | prodRes 8 x = 3} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 3}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 3} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 3}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e4 : uEnt {x ∈ box 8 | prodRes 8 x = 4} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 4}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 4} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 4}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e5 : uEnt {x ∈ box 8 | prodRes 8 x = 5} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 5}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 5} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 5}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e6 : uEnt {x ∈ box 8 | prodRes 8 x = 6} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 6}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 6} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 6}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e7 : uEnt {x ∈ box 8 | prodRes 8 x = 7} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ box 8 | prodRes 8 x = 7}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ box 8 | prodRes 8 x = 7} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 8 | prodRes 8 x = 7}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (box 8).card = 64 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 0}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 1}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 2}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 3}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 4}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 5}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 6}) = 8 from by decide,
    show (#{x ∈ box 8 | prodRes 8 x = 7}) = 8 from by decide]

/-- **The `C8` type-pair channel.** -/
theorem Ipair_val_8 : Ipair 8 = (21/16 : ℝ) := by
  rw [Ipair_eq, pairEntropy_val_8, condPairEntropy_val_8]
  ring

/-! ### The abstract cyclic order `C9` -/

/-- Exact type entropy of the `C9` channel. -/
theorem typeEntropy_val_9 : typeEntropy 9 = (-8/9 : ℝ) + (4/3 : ℝ) * Real.logb 2 3 := by
  have h : ((range 9).image (ordType 9)).val.map
      (fun v => (#{x ∈ range 9 | ordType 9 x = v} : ℕ)) = (↑[1, 2, 6] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 9).card = 9 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C9` semiprime. -/
theorem pairEntropy_val_9 : pairEntropy 9 = (-184/81 : ℝ) + (8/3 : ℝ) * Real.logb 2 3 := by
  have h : ((box 9).image (typePair 9)).val.map
      (fun v => (#{q ∈ box 9 | typePair 9 q = v} : ℕ)) = (↑[1, 4, 4, 12, 24, 36] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 9).card = 81 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_9 : condPairEntropy 9 = (-28/27 : ℝ) + (14/9 : ℝ) * Real.logb 2 3 := by
  have himg : (box 9).image (prodRes 9) = range 9 := by decide
  have e0 : uEnt {x ∈ box 9 | prodRes 9 x = 0} (typePair 9) = (-8/9 : ℝ) + (4/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 0}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 0} | typePair 9 q = v} : ℕ))
        = (↑[1, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 0}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e1 : uEnt {x ∈ box 9 | prodRes 9 x = 1} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 1}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 1} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 1}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e2 : uEnt {x ∈ box 9 | prodRes 9 x = 2} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 2}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 2} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 2}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e3 : uEnt {x ∈ box 9 | prodRes 9 x = 3} (typePair 9) = (-8/9 : ℝ) + (4/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 3}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 3} | typePair 9 q = v} : ℕ))
        = (↑[1, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 3}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e4 : uEnt {x ∈ box 9 | prodRes 9 x = 4} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 4}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 4} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 4}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e5 : uEnt {x ∈ box 9 | prodRes 9 x = 5} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 5}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 5} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 5}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e6 : uEnt {x ∈ box 9 | prodRes 9 x = 6} (typePair 9) = (-8/9 : ℝ) + (4/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 6}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 6} | typePair 9 q = v} : ℕ))
        = (↑[1, 2, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 6}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e7 : uEnt {x ∈ box 9 | prodRes 9 x = 7} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 7}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 7} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 7}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e8 : uEnt {x ∈ box 9 | prodRes 9 x = 8} (typePair 9) = (-10/9 : ℝ) + (5/3 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ box 9 | prodRes 9 x = 8}).image (typePair 9)).val.map
        (fun v => (#{q ∈ {x ∈ box 9 | prodRes 9 x = 8} | typePair 9 q = v} : ℕ))
        = (↑[2, 3, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 9 | prodRes 9 x = 8}) = 9 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (box 9).card = 81 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 0}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 1}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 2}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 3}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 4}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 5}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 6}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 7}) = 9 from by decide,
    show (#{x ∈ box 9 | prodRes 9 x = 8}) = 9 from by decide]
  ring

/-- **The `C9` type-pair channel.** -/
theorem Ipair_val_9 : Ipair 9 = (-100/81 : ℝ) + (10/9 : ℝ) * Real.logb 2 3 := by
  rw [Ipair_eq, pairEntropy_val_9, condPairEntropy_val_9]
  ring

/-! ### The abstract cyclic order `C15` -/

/-- Exact type entropy of the `C15` channel. -/
theorem typeEntropy_val_15 : typeEntropy 15 = (-34/15 : ℝ) + (1 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have h : ((range 15).image (ordType 15)).val.map
      (fun v => (#{x ∈ range 15 | ordType 15 x = v} : ℕ)) = (↑[1, 2, 4, 8] : Multiset ℕ) := by decide
  rw [typeEntropy, uEnt_eq_countSum _ _ _ h, show (range 15).card = 15 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact entropy of the unordered type pair of a `C15` semiprime. -/
theorem pairEntropy_val_15 : pairEntropy 15 = (-232/45 : ℝ) + (2 : ℝ) * Real.logb 2 3 + (2 : ℝ) * Real.logb 2 5 := by
  have h : ((box 15).image (typePair 15)).val.map
      (fun v => (#{q ∈ box 15 | typePair 15 q = v} : ℕ)) = (↑[1, 4, 4, 8, 16, 16, 16, 32, 64, 64] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (box 15).card = 225 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  ring

/-- Exact conditional entropy of the type pair given the residue of the product. -/
theorem condPairEntropy_val_15 : condPairEntropy 15 = (-262/225 : ℝ) + (13/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have himg : (box 15).image (prodRes 15) = range 15 := by decide
  have e0 : uEnt {x ∈ box 15 | prodRes 15 x = 0} (typePair 15) = (-34/15 : ℝ) + (1 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 0}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 0} | typePair 15 q = v} : ℕ))
        = (↑[1, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 0}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e1 : uEnt {x ∈ box 15 | prodRes 15 x = 1} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 1}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 1} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 1}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e2 : uEnt {x ∈ box 15 | prodRes 15 x = 2} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 2}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 2} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 2}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e3 : uEnt {x ∈ box 15 | prodRes 15 x = 3} (typePair 15) = (-16/15 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 3}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 3} | typePair 15 q = v} : ℕ))
        = (↑[2, 3, 4, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 3}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e4 : uEnt {x ∈ box 15 | prodRes 15 x = 4} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 4}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 4} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 4}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e5 : uEnt {x ∈ box 15 | prodRes 15 x = 5} (typePair 15) = (-34/15 : ℝ) + (1 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 5}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 5} | typePair 15 q = v} : ℕ))
        = (↑[1, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 5}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e6 : uEnt {x ∈ box 15 | prodRes 15 x = 6} (typePair 15) = (-16/15 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 6}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 6} | typePair 15 q = v} : ℕ))
        = (↑[2, 3, 4, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 6}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e7 : uEnt {x ∈ box 15 | prodRes 15 x = 7} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 7}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 7} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 7}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e8 : uEnt {x ∈ box 15 | prodRes 15 x = 8} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 8}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 8} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 8}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e9 : uEnt {x ∈ box 15 | prodRes 15 x = 9} (typePair 15) = (-16/15 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 9}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 9} | typePair 15 q = v} : ℕ))
        = (↑[2, 3, 4, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 9}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e10 : uEnt {x ∈ box 15 | prodRes 15 x = 10} (typePair 15) = (-34/15 : ℝ) + (1 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 10}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 10} | typePair 15 q = v} : ℕ))
        = (↑[1, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 10}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e11 : uEnt {x ∈ box 15 | prodRes 15 x = 11} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 11}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 11} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 11}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e12 : uEnt {x ∈ box 15 | prodRes 15 x = 12} (typePair 15) = (-16/15 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 12}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 12} | typePair 15 q = v} : ℕ))
        = (↑[2, 3, 4, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 12}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e13 : uEnt {x ∈ box 15 | prodRes 15 x = 13} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 13}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 13} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 13}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e14 : uEnt {x ∈ box 15 | prodRes 15 x = 14} (typePair 15) = (-4/5 : ℝ) + (2/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ box 15 | prodRes 15 x = 14}).image (typePair 15)).val.map
        (fun v => (#{q ∈ {x ∈ box 15 | prodRes 15 x = 14} | typePair 15 q = v} : ℕ))
        = (↑[2, 2, 2, 3, 6] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ box 15 | prodRes 15 x = 14}) = 15 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (box 15).card = 225 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 0}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 1}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 2}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 3}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 4}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 5}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 6}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 7}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 8}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 9}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 10}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 11}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 12}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 13}) = 15 from by decide,
    show (#{x ∈ box 15 | prodRes 15 x = 14}) = 15 from by decide]
  ring

/-- **The `C15` type-pair channel.** -/
theorem Ipair_val_15 : Ipair 15 = (-898/225 : ℝ) + (37/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  rw [Ipair_eq, pairEntropy_val_15, condPairEntropy_val_15]
  ring

/-! ### CRT additivity of the type-pair information

For coprime cyclic orders the information carried by the unordered type pair of
a semiprime splits as a sum over the primary components. -/

/-- `I_pair(6) = I_pair(2) + I_pair(3)`. -/
theorem Ipair_crt_two_three : Ipair 6 = Ipair 2 + Ipair 3 := by
  rw [Ipair_val_6, Ipair_val_2, Ipair_val_3]; ring

/-- `I_pair(10) = I_pair(2) + I_pair(5)`. -/
theorem Ipair_crt_two_five : Ipair 10 = Ipair 2 + Ipair 5 := by
  rw [Ipair_val_10, Ipair_val_2, Ipair_val_5]; ring

/-- `I_pair(12) = I_pair(4) + I_pair(3)`. -/
theorem Ipair_crt_four_three : Ipair 12 = Ipair 4 + Ipair 3 := by
  rw [Ipair_val_12, Ipair_val_4, Ipair_val_3]; ring

/-- `I_pair(15) = I_pair(3) + I_pair(5)`. -/
theorem Ipair_crt_three_five : Ipair 15 = Ipair 3 + Ipair 5 := by
  rw [Ipair_val_15, Ipair_val_3, Ipair_val_5]; ring

/-! ### Evenness, not compositeness, is what breaks the cap -/

/-- The purely `2`-primary order `8` is above the binary-fork cap. -/
theorem one_lt_Ipair_eight : 1 < Ipair 8 := by
  rw [Ipair_val_8]; norm_num

/-- The odd order `3` is strictly below the binary-fork cap. -/
theorem Ipair_three_lt_one : Ipair 3 < 1 := by
  have h3 := lb_three_lt
  rw [Ipair_val_3]; linarith

/-- The odd order `5` is strictly below the binary-fork cap. -/
theorem Ipair_five_lt_one : Ipair 5 < 1 := by
  have h3 := lb_three_lt
  have h5 := lb_five_lt
  rw [Ipair_val_5]; linarith

/-- The odd (composite, non-squarefree) order `9` is strictly below the cap. -/
theorem Ipair_nine_lt_one : Ipair 9 < 1 := by
  have h3 := lb_three_lt
  rw [Ipair_val_9]; linarith

/-- The odd (composite, squarefree) order `15` is strictly below the cap. -/
theorem Ipair_fifteen_lt_one : Ipair 15 < 1 := by
  have h3 := lb_three_lt
  have h5 := lb_five_lt
  rw [Ipair_val_15]; linarith

/-- **Compositeness is not the trigger.**  The order `15` is composite with two
distinct prime factors, yet its type-pair channel stays below one bit, whereas
the prime-power order `8` exceeds it.  Hence no monotone function of the number
of divisors can govern the cap. -/
theorem cap_not_governed_by_compositeness :
    Ipair 15 < 1 ∧ 1 < Ipair 8 :=
  ⟨Ipair_fifteen_lt_one, one_lt_Ipair_eight⟩

/-- **All odd orders computed here are below the cap, all even ones above (or at)
it.**  This suggests that the order-two element is the source of the above-cap
behaviour — a reading that is *refuted* in `Shared.CyclicTypeChannelOdd`, where
an explicit odd order with `Ipair > 1` is produced by accumulating sixteen odd
primary parts. -/
theorem odd_orders_below_cap :
    Ipair 3 < 1 ∧ Ipair 5 < 1 ∧ Ipair 9 < 1 ∧ Ipair 15 < 1 :=
  ⟨Ipair_three_lt_one, Ipair_five_lt_one, Ipair_nine_lt_one, Ipair_fifteen_lt_one⟩

/-! ### A value beyond the reach of enumeration

`n = 60` has a sample box of `3600` pairs, out of reach of direct kernel
enumeration; the CRT law computes it from the primary parts `4` and `15`. -/

/-- Exact value of the three-primary order `60`, obtained from the CRT law. -/
theorem Ipair_val_60 :
    Ipair 60 = (-2467/900 : ℝ) + (37/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have h : Ipair (4 * 15) = Ipair 4 + Ipair 15 :=
    Ipair_mul_of_coprime (by norm_num) (by norm_num) (by decide)
  rw [show (60 : ℕ) = 4 * 15 from by norm_num, h, Ipair_val_4, Ipair_val_15]
  ring

/-- The three-primary order `60` carries more than `7/4` bits — far above the
binary-fork cap, and beyond every value in the enumerated table. -/
theorem Ipair_sixty_gt : (7 : ℝ) / 4 < Ipair 60 := by
  have h3 := lb_three_gt
  have h5 := lb_five_gt
  rw [Ipair_val_60]
  linarith

end CyclicTypeChannel
-- ==== upstream: Catalog/Shared/CyclicTypeChannelPrime.lean ====
/-
# The prime cyclic order: a closed form for the type-pair channel

The exact-value files compute the type-pair channel `Ipair n` for a finite list of
cyclic orders.  This file closes the *prime* case in complete generality: for
every prime `p` the channel of the cyclic order `C p` is

  `Ipair p = log₂ p - (p-1)(2p-1)/p² · log₂ (p-1) + (p-1)(p-2)/p² · log₂ (p-2)`.

(`Ipair_prime`; the two exact values `Ipair 3` and `Ipair 5` recorded in
`CyclicTypeChannelCRT.lean` are the instances `p = 3, 5`.)

Two consequences:

* `Ipair_prime_lt_one`: every **odd** prime order is *strictly below* the one-bit
  binary-fork cap, so among prime cyclic orders the cap is attained exactly at
  `p = 2` (`Ipair_prime_eq_one_iff`).  This upgrades the isolated computations
  `Ipair 3 < 1`, `Ipair 5 < 1` to an infinite statement and shows that the
  above-cap phenomenon of `C₄, C₆, C₁₀, C₁₂, C₁₆` is genuinely a *composite*
  phenomenon: a prime cyclic order has only two splitting types, and its fork is
  exactly the binary fork that papers 72–74 capped.
* `above_cap_imp_not_prime`: breaking the cap forces the cyclic order to be
  composite.
-/


namespace CyclicTypeChannel

open Finset

/-! ## 1. The splitting type of a prime cyclic order -/

/-- For a prime order `p` the splitting type is binary: the exponent `0` gives the
split-completely type `1`, every other exponent gives the inert type `p`. -/
lemma ordType_prime {p a : ℕ} (hp : p.Prime) (ha : a < p) :
    ordType p a = if a = 0 then 1 else p := by
  rcases eq_or_ne a 0 with rfl | h
  · simp [ordType_zero hp.pos]
  · have hnd : ¬ p ∣ a := fun hdvd => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd
      omega
    have hco : Nat.gcd a p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    simp [ordType, hco, h]

/-- The unordered type pair for a prime cyclic order. -/
lemma typePair_prime {p a b : ℕ} (hp : p.Prime) (ha : a < p) (hb : b < p) :
    typePair p (a, b) =
      if a = 0 ∧ b = 0 then (1, 1) else if a = 0 ∨ b = 0 then (1, p) else (p, p) := by
  have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
  simp only [typePair, ordType_prime hp ha, ordType_prime hp hb]
  rcases eq_or_ne a 0 with rfl | ha0
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp
    · simp [hb0, min_eq_left h1, max_eq_right h1]
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp [ha0, min_eq_right h1, max_eq_left h1]
    · simp [ha0, hb0]

lemma mem_box_iff {n : ℕ} {x : ℕ × ℕ} : x ∈ box n ↔ x.1 < n ∧ x.2 < n := by
  simp [box, Finset.mem_product]

lemma card_box (n : ℕ) : (box n).card = n * n := by
  simp [box]

/-! ## 2. The three fibres in the box -/

/-- The nonzero exponents. -/
-- [dropped: platform already declares nz]
private lemma card_nz {p : ℕ} (hp : 0 < p) : (nz p).card = p - 1 := by
  simp [nz, Finset.card_erase_of_mem, hp]

private lemma mem_nz {p a : ℕ} : a ∈ nz p ↔ a < p ∧ a ≠ 0 := by
  simp [nz, and_comm]

lemma box_fiber_11 {p : ℕ} (hp : p.Prime) :
    {x ∈ box p | typePair p x = (1, 1)} = {(0, 0)} := by
  have hpne : p ≠ 1 := hp.ne_one
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    rw [typePair_prime hp ha hb] at h
    by_cases h0 : a = 0 ∧ b = 0
    · exact h0
    · exfalso
      rw [if_neg h0] at h
      by_cases h1 : a = 0 ∨ b = 0
      · rw [if_pos h1, Prod.mk.injEq] at h
        exact hpne h.2
      · rw [if_neg h1, Prod.mk.injEq] at h
        exact hpne h.1
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨hp.pos, hp.pos⟩, by rw [typePair_prime hp hp.pos hp.pos]; simp⟩

lemma box_fiber_1p {p : ℕ} (hp : p.Prime) :
    {x ∈ box p | typePair p x = (1, p)} = ({0} ×ˢ nz p) ∪ (nz p ×ˢ {0}) := by
  have hpne : p ≠ 1 := hp.ne_one
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, mem_nz]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    rw [typePair_prime hp ha hb] at h
    by_cases h0 : a = 0 ∧ b = 0
    · exfalso
      rw [if_pos h0, Prod.mk.injEq] at h
      exact hpne h.2.symm
    · rw [if_neg h0] at h
      by_cases h1 : a = 0 ∨ b = 0
      · rcases h1 with rfl | rfl
        · have hb0 : b ≠ 0 := fun hb0 => h0 ⟨rfl, hb0⟩
          tauto
        · have ha0 : a ≠ 0 := fun ha0 => h0 ⟨ha0, rfl⟩
          tauto
      · exfalso
        rw [if_neg h1, Prod.mk.injEq] at h
        exact hpne h.1
  · rintro (⟨rfl, hb, hb0⟩ | ⟨⟨ha, ha0⟩, rfl⟩)
    · refine ⟨⟨hp.pos, hb⟩, ?_⟩
      rw [typePair_prime hp hp.pos hb]
      simp [hb0]
    · refine ⟨⟨ha, hp.pos⟩, ?_⟩
      rw [typePair_prime hp ha hp.pos]
      simp [ha0]

lemma box_fiber_pp {p : ℕ} (hp : p.Prime) :
    {x ∈ box p | typePair p x = (p, p)} = nz p ×ˢ nz p := by
  have hpne : p ≠ 1 := hp.ne_one
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_product, mem_nz]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    rw [typePair_prime hp ha hb] at h
    by_cases h0 : a = 0 ∧ b = 0
    · exfalso
      rw [if_pos h0, Prod.mk.injEq] at h
      exact hpne h.1.symm
    · rw [if_neg h0] at h
      by_cases h1 : a = 0 ∨ b = 0
      · exfalso
        rw [if_pos h1, Prod.mk.injEq] at h
        exact hpne h.1.symm
      · push_neg at h1
        exact ⟨⟨ha, h1.1⟩, hb, h1.2⟩
  · rintro ⟨⟨ha, ha0⟩, hb, hb0⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    rw [typePair_prime hp ha hb]
    simp [ha0, hb0]

lemma card_box_fiber_11 {p : ℕ} (hp : p.Prime) :
    #{x ∈ box p | typePair p x = (1, 1)} = 1 := by
  rw [box_fiber_11 hp, Finset.card_singleton]

lemma card_box_fiber_1p {p : ℕ} (hp : p.Prime) :
    #{x ∈ box p | typePair p x = (1, p)} = 2 * (p - 1) := by
  have hdisj : Disjoint (({0} : Finset ℕ) ×ˢ nz p) (nz p ×ˢ ({0} : Finset ℕ)) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton, mem_nz] at h1 h2
    exact h2.1.2 h1.1
  rw [box_fiber_1p hp, Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product, Finset.card_singleton, card_nz hp.pos]
  ring

lemma card_box_fiber_pp {p : ℕ} (hp : p.Prime) :
    #{x ∈ box p | typePair p x = (p, p)} = (p - 1) * (p - 1) := by
  rw [box_fiber_pp hp, Finset.card_product, card_nz hp.pos]

lemma image_typePair_prime {p : ℕ} (hp : p.Prime) :
    (box p).image (typePair p) = {(1, 1), (1, p), (p, p)} := by
  ext v
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [mem_box_iff] at hx
    rw [typePair_prime hp hx.1 hx.2]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · have h00 : ((0 : ℕ), (0 : ℕ)) ∈ box p := by
      rw [mem_box_iff]; exact ⟨hp.pos, hp.pos⟩
    have h01 : ((0 : ℕ), (1 : ℕ)) ∈ box p := by
      rw [mem_box_iff]; exact ⟨hp.pos, hp.one_lt⟩
    have h11 : ((1 : ℕ), (1 : ℕ)) ∈ box p := by
      rw [mem_box_iff]; exact ⟨hp.one_lt, hp.one_lt⟩
    rintro (rfl | rfl | rfl)
    · exact ⟨(0, 0), h00, by rw [typePair_prime hp hp.pos hp.pos]; simp⟩
    · exact ⟨(0, 1), h01, by rw [typePair_prime hp hp.pos hp.one_lt]; simp⟩
    · exact ⟨(1, 1), h11, by rw [typePair_prime hp hp.one_lt hp.one_lt]; simp⟩

/-! ## 3. The pair entropy -/

lemma uEnt_eq_image_sum {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) :
    uEnt s g = Real.logb 2 s.card
      - (∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ))
        / s.card := by
  rw [uEnt, sum_logb_fiber]

/-- **The pair entropy of a prime cyclic order.** -/
theorem pairEntropy_prime {p : ℕ} (hp : p.Prime) :
    pairEntropy p = 2 * Real.logb 2 p - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - 2 * ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) := by
  have hpne : p ≠ 1 := hp.ne_one
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hne1 : ((1 : ℕ), (1 : ℕ)) ≠ ((1 : ℕ), p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.2.symm
  have hne2 : ((1 : ℕ), (1 : ℕ)) ≠ (p, p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.1.symm
  have hne3 : ((1 : ℕ), p) ≠ (p, p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.1.symm
  have hmem1 : ((1 : ℕ), (1 : ℕ)) ∉ ({((1 : ℕ), p), (p, p)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hne1, hne2⟩
  have hmem2 : ((1 : ℕ), p) ∉ ({(p, p)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    exact hne3
  rw [pairEntropy, uEnt_eq_image_sum, image_typePair_prime hp, card_box,
    Finset.sum_insert hmem1, Finset.sum_insert hmem2,
    Finset.sum_singleton, card_box_fiber_11 hp, card_box_fiber_1p hp, card_box_fiber_pp hp]
  push_cast [hcast]
  have e1 : Real.logb 2 (2 * ((p : ℝ) - 1)) = 1 + Real.logb 2 ((p : ℝ) - 1) := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt hpm1)]
    simp
  have e2 : Real.logb 2 (((p : ℝ) - 1) * ((p : ℝ) - 1)) = 2 * Real.logb 2 ((p : ℝ) - 1) := by
    rw [Real.logb_mul (ne_of_gt hpm1) (ne_of_gt hpm1)]; ring
  have e3 : Real.logb 2 ((p : ℝ) * p) = 2 * Real.logb 2 p := by
    rw [Real.logb_mul (ne_of_gt hp0) (ne_of_gt hp0)]; ring
  rw [e1, e2, e3, Real.logb_one]
  field_simp
  ring

/-! ## 4. The conditional entropy -/

lemma prodRes_fiber {p c : ℕ} (hp : 0 < p) (hc : c < p) :
    {x ∈ box p | prodRes p x = c} = (range p).image (fun a => (a, (c + p - a) % p)) := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨a, ha, rfl, ?_⟩
    rw [prodRes] at h
    rcases lt_or_ge (a + b) p with hab | hab
    · have hc' : c = a + b := by rw [← h, Nat.mod_eq_of_lt hab]
      have e : c + p - a = b + p := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    · have hlt : a + b - p < p := by omega
      have hc' : c = a + b - p := by
        rw [← h, Nat.mod_eq_sub_mod hab, Nat.mod_eq_of_lt hlt]
      have e : c + p - a = b := by omega
      rw [e, Nat.mod_eq_of_lt hb]
  · rintro ⟨a', ha', rfl, rfl⟩
    refine ⟨⟨ha', Nat.mod_lt _ hp⟩, ?_⟩
    rw [prodRes]
    rcases Nat.lt_or_ge c a' with h | h
    · have e : c + p - a' < p := by omega
      rw [Nat.mod_eq_of_lt e]
      have e2 : a' + (c + p - a') = c + p := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
    · have e : c + p - a' = (c - a') + p := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : c - a' < p)]
      have e2 : a' + (c - a') = c := by omega
      rw [e2, Nat.mod_eq_of_lt hc]

lemma card_prodRes_fiber {p c : ℕ} (hp : 0 < p) (hc : c < p) :
    #{x ∈ box p | prodRes p x = c} = p := by
  rw [prodRes_fiber hp hc, Finset.card_image_of_injective _ (fun x y h => by
    simpa using congrArg Prod.fst h), Finset.card_range]

lemma image_prodRes {p : ℕ} (hp : 0 < p) : (box p).image (prodRes p) = range p := by
  ext c
  simp only [Finset.mem_image, mem_range]
  constructor
  · rintro ⟨x, _, rfl⟩
    exact Nat.mod_lt _ hp
  · intro hc
    exact ⟨(c, 0), by rw [mem_box_iff]; exact ⟨hc, hp⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩

/-- On the `N ≡ 0` fibre either both exponents vanish or neither does. -/
lemma prodRes_zero_dichotomy {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : prodRes p (a, b) = 0) : (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b ≠ 0) := by
  rcases eq_or_ne a 0 with rfl | h1
  · refine Or.inl ⟨rfl, ?_⟩
    simpa [prodRes, Nat.mod_eq_of_lt hb] using h
  · rcases eq_or_ne b 0 with rfl | h2
    · exact absurd (by simpa [prodRes, Nat.mod_eq_of_lt ha] using h) h1
    · exact Or.inr ⟨h1, h2⟩

/-- On a nonzero fibre either exactly one exponent vanishes, or neither does. -/
lemma prodRes_ne_zero_dichotomy {p a b c : ℕ} (ha : a < p) (hb : b < p)
    (h : prodRes p (a, b) = c) :
    ((a, b) = (0, c) ∨ (a, b) = (c, 0)) ∨ (a ≠ 0 ∧ b ≠ 0) := by
  rcases eq_or_ne a 0 with rfl | h1
  · refine Or.inl (Or.inl ?_)
    have : b = c := by simpa [prodRes, Nat.mod_eq_of_lt hb] using h
    simp [this]
  · rcases eq_or_ne b 0 with rfl | h2
    · refine Or.inl (Or.inr ?_)
      have : a = c := by simpa [prodRes, Nat.mod_eq_of_lt ha] using h
      simp [this]
    · exact Or.inr ⟨h1, h2⟩

lemma zero_fiber_11 {p : ℕ} (hp : p.Prime) :
    {x ∈ {y ∈ box p | prodRes p y = 0} | typePair p x = (1, 1)} = {(0, 0)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, _⟩, h⟩
    have hmem : (a, b) ∈ {x ∈ box p | typePair p x = (1, 1)} := by
      rw [mem_filter, mem_box_iff]; exact ⟨⟨ha, hb⟩, h⟩
    rw [box_fiber_11 hp, Finset.mem_singleton] at hmem
    exact ⟨congrArg Prod.fst hmem, congrArg Prod.snd hmem⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨⟨hp.pos, hp.pos⟩, by simp [prodRes]⟩, ?_⟩
    rw [typePair_prime hp hp.pos hp.pos]; simp

lemma origin_mem_zero_fiber {p : ℕ} (hp : p.Prime) :
    ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)) ⊆ {y ∈ box p | prodRes p y = 0} := by
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  rw [mem_filter, mem_box_iff]
  exact ⟨⟨hp.pos, hp.pos⟩, by simp [prodRes]⟩

lemma zero_fiber_pp {p : ℕ} (hp : p.Prime) :
    #{x ∈ {y ∈ box p | prodRes p y = 0} | typePair p x = (p, p)} = p - 1 := by
  have hpne : p ≠ 1 := hp.ne_one
  have hsub : {x ∈ {y ∈ box p | prodRes p y = 0} | typePair p x = (p, p)}
      = {y ∈ box p | prodRes p y = 0} \ {(0, 0)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_box_iff, Finset.mem_sdiff, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨rfl, rfl⟩
      rw [typePair_prime hp hp.pos hp.pos] at h2
      simp only [and_self, if_true, Prod.mk.injEq] at h2
      exact hpne h2.symm
    · rintro ⟨⟨⟨ha, hb⟩, hres⟩, hne⟩
      refine ⟨⟨⟨ha, hb⟩, hres⟩, ?_⟩
      rw [typePair_prime hp ha hb]
      rcases prodRes_zero_dichotomy ha hb hres with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
      · exact absurd ⟨rfl, rfl⟩ hne
      · rw [if_neg (by tauto), if_neg (by tauto)]
  rw [hsub, Finset.card_sdiff_of_subset (origin_mem_zero_fiber hp), Finset.card_singleton,
    card_prodRes_fiber hp.pos hp.pos]

lemma image_zero_fiber {p : ℕ} (hp : p.Prime) :
    ({y ∈ box p | prodRes p y = 0}).image (typePair p) = {(1, 1), (p, p)} := by
  have hp2 : 2 ≤ p := hp.two_le
  ext v
  simp only [Finset.mem_image, mem_filter, mem_box_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨⟨ha, hb⟩, hres⟩, rfl⟩⟩
    rw [typePair_prime hp ha hb]
    rcases prodRes_zero_dichotomy ha hb hres with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · simp
    · rw [if_neg (by tauto), if_neg (by tauto)]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(0, 0), ⟨⟨⟨hp.pos, hp.pos⟩, by simp [prodRes]⟩, by
        rw [typePair_prime hp hp.pos hp.pos]; simp⟩⟩
    · refine ⟨(1, p - 1), ⟨⟨⟨hp.one_lt, by omega⟩, ?_⟩, ?_⟩⟩
      · rw [prodRes]
        have e : 1 + (p - 1) = p := by omega
        rw [e, Nat.mod_self]
      · rw [typePair_prime hp hp.one_lt (by omega)]
        have h2 : p - 1 ≠ 0 := by omega
        rw [if_neg (by tauto), if_neg (by tauto)]

/-- The entropy of the type pair on the `N ≡ 0` fibre. -/
theorem uEnt_zero_fiber {p : ℕ} (hp : p.Prime) :
    uEnt {y ∈ box p | prodRes p y = 0} (typePair p)
      = Real.logb 2 p - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) := by
  have hpne : p ≠ 1 := hp.ne_one
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hne : ((1 : ℕ), (1 : ℕ)) ≠ (p, p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.1.symm
  have hmem : ((1 : ℕ), (1 : ℕ)) ∉ ({(p, p)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]; exact hne
  have h11 : #{x ∈ {y ∈ box p | prodRes p y = 0} | typePair p x = (1, 1)} = 1 := by
    rw [zero_fiber_11 hp, Finset.card_singleton]
  rw [uEnt_eq_image_sum, image_zero_fiber hp, card_prodRes_fiber hp.pos hp.pos,
    Finset.sum_insert hmem, Finset.sum_singleton, h11, zero_fiber_pp hp]
  push_cast [hcast]
  simp

/-! ### The nonzero fibres -/

lemma nonzero_fiber_1p {p c : ℕ} (hp : p.Prime) (hc : c < p) (hc0 : c ≠ 0) :
    {x ∈ {y ∈ box p | prodRes p y = c} | typePair p x = (1, p)} = {(0, c), (c, 0)} := by
  have hpne : p ≠ 1 := hp.ne_one
  ext ⟨a, b⟩
  simp only [mem_filter, mem_box_iff, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hres⟩, h⟩
    rcases prodRes_ne_zero_dichotomy ha hb hres with hcase | ⟨h1, h2⟩
    · rcases hcase with hcase | hcase
      · exact Or.inl ⟨congrArg Prod.fst hcase, congrArg Prod.snd hcase⟩
      · exact Or.inr ⟨congrArg Prod.fst hcase, congrArg Prod.snd hcase⟩
    · exfalso
      rw [typePair_prime hp ha hb, if_neg (by tauto), if_neg (by tauto), Prod.mk.injEq] at h
      exact hpne h.1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨⟨⟨hp.pos, hc⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩, ?_⟩
      rw [typePair_prime hp hp.pos hc, if_neg (by tauto), if_pos (by tauto)]
    · refine ⟨⟨⟨hc, hp.pos⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩, ?_⟩
      rw [typePair_prime hp hc hp.pos, if_neg (by tauto), if_pos (by tauto)]

lemma card_nonzero_fiber_1p {p c : ℕ} (hp : p.Prime) (hc : c < p) (hc0 : c ≠ 0) :
    #{x ∈ {y ∈ box p | prodRes p y = c} | typePair p x = (1, p)} = 2 := by
  have hne : ((0 : ℕ), c) ∉ ({(c, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    exact fun h => hc0 h.1.symm
  rw [nonzero_fiber_1p hp hc hc0, Finset.card_insert_of_notMem hne, Finset.card_singleton]

lemma pair_mem_nonzero_fiber {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    ({((0 : ℕ), c), (c, 0)} : Finset (ℕ × ℕ)) ⊆ {y ∈ box p | prodRes p y = c} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_filter, mem_box_iff]
  rcases hx with rfl | rfl
  · exact ⟨⟨hp.pos, hc⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩
  · exact ⟨⟨hc, hp.pos⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩

lemma card_nonzero_fiber_pp {p c : ℕ} (hp : p.Prime) (hc : c < p) (hc0 : c ≠ 0) :
    #{x ∈ {y ∈ box p | prodRes p y = c} | typePair p x = (p, p)} = p - 2 := by
  have hpne : p ≠ 1 := hp.ne_one
  have hne : ((0 : ℕ), c) ∉ ({(c, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    exact fun h => hc0 h.1.symm
  have hsub : {x ∈ {y ∈ box p | prodRes p y = c} | typePair p x = (p, p)}
      = {y ∈ box p | prodRes p y = c} \ {(0, c), (c, 0)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_box_iff, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hres⟩, h⟩
      refine ⟨⟨⟨ha, hb⟩, hres⟩, ?_⟩
      rw [typePair_prime hp ha hb] at h
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [if_neg (by tauto), if_pos (by tauto), Prod.mk.injEq] at h
        exact hpne h.1.symm
      · rw [if_neg (by tauto), if_pos (by tauto), Prod.mk.injEq] at h
        exact hpne h.1.symm
    · rintro ⟨⟨⟨ha, hb⟩, hres⟩, hne'⟩
      refine ⟨⟨⟨ha, hb⟩, hres⟩, ?_⟩
      rw [typePair_prime hp ha hb]
      rcases prodRes_ne_zero_dichotomy ha hb hres with hcase | ⟨h1, h2⟩
      · exfalso
        rcases hcase with hcase | hcase
        · exact hne' (Or.inl ⟨congrArg Prod.fst hcase, congrArg Prod.snd hcase⟩)
        · exact hne' (Or.inr ⟨congrArg Prod.fst hcase, congrArg Prod.snd hcase⟩)
      · rw [if_neg (by tauto), if_neg (by tauto)]
  rw [hsub, Finset.card_sdiff_of_subset (pair_mem_nonzero_fiber hp hc), card_prodRes_fiber hp.pos hc,
    Finset.card_insert_of_notMem hne, Finset.card_singleton]

lemma image_nonzero_fiber {p c : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hc : c < p) (hc0 : c ≠ 0) :
    ({y ∈ box p | prodRes p y = c}).image (typePair p) = {(1, p), (p, p)} := by
  ext v
  simp only [Finset.mem_image, mem_filter, mem_box_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨⟨ha, hb⟩, hres⟩, rfl⟩⟩
    rw [typePair_prime hp ha hb]
    rcases prodRes_ne_zero_dichotomy ha hb hres with hcase | ⟨h1, h2⟩
    · rcases hcase with hcase | hcase <;>
        · rw [Prod.mk.injEq] at hcase
          obtain ⟨rfl, rfl⟩ := hcase
          rw [if_neg (by tauto), if_pos (by tauto)]
          exact Or.inl rfl
    · rw [if_neg (by tauto), if_neg (by tauto)]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · refine ⟨(0, c), ⟨⟨⟨hp.pos, hc⟩, by simp [prodRes, Nat.mod_eq_of_lt hc]⟩, ?_⟩⟩
      rw [typePair_prime hp hp.pos hc, if_neg (by tauto), if_pos (by tauto)]
    · -- with `p ≥ 3` there is a pair of nonzero exponents summing to `c`
      have hex : ∃ a b, a < p ∧ b < p ∧ a ≠ 0 ∧ b ≠ 0 ∧ (a + b) % p = c := by
        rcases eq_or_ne c 1 with rfl | hc1
        · refine ⟨2, p - 1, by omega, by omega, by omega, by omega, ?_⟩
          have e : 2 + (p - 1) = 1 + p := by omega
          rw [e, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        · refine ⟨1, c - 1, by omega, by omega, by omega, by omega, ?_⟩
          have e : 1 + (c - 1) = c := by omega
          rw [e, Nat.mod_eq_of_lt hc]
      obtain ⟨a, b, ha, hb, ha0, hb0, hres⟩ := hex
      refine ⟨(a, b), ⟨⟨⟨ha, hb⟩, hres⟩, ?_⟩⟩
      rw [typePair_prime hp ha hb, if_neg (by tauto), if_neg (by tauto)]

/-- The entropy of the type pair on a nonzero fibre. -/
theorem uEnt_nonzero_fiber {p c : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hc : c < p) (hc0 : c ≠ 0) :
    uEnt {y ∈ box p | prodRes p y = c} (typePair p)
      = Real.logb 2 p - (2 + ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2)) / (p : ℝ) := by
  have hpne : p ≠ 1 := hp.ne_one
  have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
  have hne : ((1 : ℕ), p) ≠ (p, p) := by
    intro h; rw [Prod.mk.injEq] at h; exact hpne h.1.symm
  have hmem : ((1 : ℕ), p) ∉ ({(p, p)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]; exact hne
  have hl2 : Real.logb 2 (2 : ℝ) = 1 := by simp
  rw [uEnt_eq_image_sum, image_nonzero_fiber hp hp3 hc hc0, card_prodRes_fiber hp.pos hc,
    Finset.sum_insert hmem, Finset.sum_singleton,
    card_nonzero_fiber_1p hp hc hc0, card_nonzero_fiber_pp hp hc hc0]
  push_cast [hcast]
  rw [hl2]
  ring

/-- **The conditional pair entropy of a prime cyclic order.** -/
theorem condPairEntropy_prime {p : ℕ} (hp : p.Prime) :
    condPairEntropy p = Real.logb 2 p
      - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by
  rcases eq_or_lt_of_le hp.two_le with h2 | h2
  · -- `p = 2`
    have hp2 : p = 2 := h2.symm
    subst hp2
    rw [condPairEntropy_val_2]
    norm_num
  · have hp3 : 3 ≤ p := by omega
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hcard : ((box p).card : ℝ) = (p : ℝ) * p := by rw [card_box]; push_cast; ring
    rw [condPairEntropy, condEnt, image_prodRes hp.pos]
    have hterm : ∀ c ∈ range p,
        ((#{x ∈ box p | prodRes p x = c} : ℝ) / (box p).card) *
            uEnt {x ∈ box p | prodRes p x = c} (typePair p)
          = (1 / (p : ℝ)) * uEnt {x ∈ box p | prodRes p x = c} (typePair p) := by
      intro c hc
      rw [mem_range] at hc
      rw [card_prodRes_fiber hp.pos hc, hcard]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsplit : ∑ c ∈ range p, uEnt {x ∈ box p | prodRes p x = c} (typePair p)
        = uEnt {x ∈ box p | prodRes p x = 0} (typePair p)
          + ∑ c ∈ (range p).erase 0, uEnt {x ∈ box p | prodRes p x = c} (typePair p) := by
      rw [← Finset.add_sum_erase _ _ (mem_range.2 hp.pos)]
    have hconst : ∀ c ∈ (range p).erase 0,
        uEnt {x ∈ box p | prodRes p x = c} (typePair p)
          = Real.logb 2 p - (2 + ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2)) / (p : ℝ) := by
      intro c hc
      rw [Finset.mem_erase, mem_range] at hc
      exact uEnt_nonzero_fiber hp hp3 hc.2 hc.1
    rw [hsplit, Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_erase_of_mem (mem_range.2 hp.pos), Finset.card_range, uEnt_zero_fiber hp]
    have hcast1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; norm_num
    rw [nsmul_eq_mul, hcast1]
    field_simp
    ring

/-- **The type-pair channel of a prime cyclic order — a closed form for every
prime.**  For `p = 2` this returns the paper-74 cap `1`; for every odd prime the
value is strictly smaller (`Ipair_prime_lt_one`). -/
theorem Ipair_prime {p : ℕ} (hp : p.Prime) :
    Ipair p = Real.logb 2 p
      - ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
      + ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Ipair_eq, pairEntropy_prime hp, condPairEntropy_prime hp]
  field_simp
  ring

/-! ## 5. Consequences: the cap among prime orders -/

/-- The elementary bound `log₂ (x+1) - log₂ x ≤ 1 / (x log 2)`. -/
lemma logb_sub_logb_le {x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 (x + 1) - Real.logb 2 x ≤ 1 / (x * Real.log 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
    rw [Real.log_div (by linarith) (ne_of_gt hx0)]
  have hle : Real.log ((x + 1) / x) ≤ 1 / x := by
    have h2 := Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)
    have hsimp : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rw [hsimp] at h2
    exact h2
  have hgoal : Real.log ((x + 1) / x) / Real.log 2 ≤ (1 / x) / Real.log 2 := by
    gcongr
  rw [Real.logb, Real.logb, div_sub_div_same, h]
  calc Real.log ((x + 1) / x) / Real.log 2 ≤ (1 / x) / Real.log 2 := hgoal
    _ = 1 / (x * Real.log 2) := by field_simp

/-- `log₂ p ≤ p`. -/
lemma logb_two_le_self {p : ℕ} (hp : 0 < p) : Real.logb 2 (p : ℝ) ≤ (p : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (p : ℝ) ≤ 2 ^ p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have h2 : Real.log (p : ℝ) ≤ Real.log ((2 : ℝ) ^ p) :=
    Real.log_le_log (by exact_mod_cast hp) h1
  rw [Real.log_pow] at h2
  rw [Real.logb, div_le_iff₀ hlog2]
  calc Real.log (p : ℝ) ≤ (p : ℕ) * Real.log 2 := h2
    _ = (p : ℝ) * Real.log 2 := by ring

/-- **Every odd prime cyclic order stays strictly below the one-bit cap.**
Together with `Ipair 2 = 1` this pins the binary-fork cap to the single prime
order `p = 2`: the above-cap behaviour of `C₄, C₆, C₁₀, C₁₂, C₁₆` is a composite
phenomenon. -/
theorem Ipair_prime_lt_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Ipair p < 1 := by
  have hp3 : 3 ≤ p := by
    have h := hp.two_le
    rcases eq_or_lt_of_le h with h' | h'
    · exact absurd h'.symm hp2
    · omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  set L := Real.logb 2 (p : ℝ) with hL
  set L1 := Real.logb 2 ((p : ℝ) - 1) with hL1
  set L2 := Real.logb 2 ((p : ℝ) - 2) with hL2
  set A := ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 with hA
  set B := ((p : ℝ) - 1) * ((p : ℝ) - 2) / (p : ℝ) ^ 2 with hB
  -- the first-order bound on the marginal gap
  have hkey : L - L1 ≤ 1 / (((p : ℝ) - 1) * Real.log 2) := by
    have h := logb_sub_logb_le (x := (p : ℝ) - 1) (by linarith)
    have e : (p : ℝ) - 1 + 1 = (p : ℝ) := by ring
    rw [e] at h
    exact h
  have hApos : 0 ≤ A := by
    rw [hA]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hBpos : 0 ≤ B := by
    rw [hB]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hL2le : L2 ≤ L := by
    rw [hL2, hL]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  -- the algebraic decomposition of the channel
  have hdecomp : Ipair p = L * (1 - A + B) + A * (L - L1) - B * (L - L2) := by
    rw [Ipair_prime hp, hA, hB, hL, hL1, hL2]
    field_simp
    ring
  have hcoeff : 1 - A + B = 1 / (p : ℝ) ^ 2 := by
    rw [hA, hB]
    field_simp
    ring
  have hne1' : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hne2' : (p : ℝ) ≠ 0 := by linarith
  have hne3' : Real.log 2 ≠ 0 := by linarith
  have hstep1 : A * (L - L1) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    calc A * (L - L1) ≤ A * (1 / (((p : ℝ) - 1) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hkey hApos
      _ = (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
          rw [hA]; field_simp
  have hstep2 : 0 ≤ B * (L - L2) := mul_nonneg hBpos (by linarith)
  have hIle : Ipair p ≤ L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    rw [hdecomp, hcoeff]
    have : L * (1 / (p : ℝ) ^ 2) = L / (p : ℝ) ^ 2 := by ring
    linarith [hstep1, hstep2, this]
  -- the numerical bound
  have hnum : L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) < 1 := by
    have hcollect : L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2)
        = (L + (2 * (p : ℝ) - 1) / Real.log 2) / (p : ℝ) ^ 2 := by
      field_simp
    rw [hcollect, div_lt_one (by positivity)]
    have hq : (2 * (p : ℝ) - 1) / Real.log 2 < (2 * (p : ℝ) - 1) / 0.6931471803 :=
      div_lt_div_of_pos_left (by linarith) (by norm_num) hlog2
    rcases eq_or_lt_of_le hp3 with h3 | h3
    · -- `p = 3`
      have hp3' : p = 3 := h3.symm
      subst hp3'
      have hLlt : L < 8 / 5 := by
        rw [hL]
        have : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
        rw [this]
        exact lb_three_lt
      have hcast3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
      rw [hcast3] at hq ⊢
      norm_num at hq ⊢
      linarith
    · -- `p ≥ 4`
      have hp4 : (4 : ℝ) ≤ (p : ℝ) := by
        have : 4 ≤ p := by omega
        exact_mod_cast this
      have hLle : L ≤ (p : ℝ) := by rw [hL]; exact logb_two_le_self hp.pos
      have hlin : (2 * (p : ℝ) - 1) / 0.6931471803 ≤ 2.8854 * (p : ℝ) - 1.4427 := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      nlinarith
  linarith

/-- **Among prime cyclic orders the cap is attained exactly at `p = 2`.** -/
theorem Ipair_prime_eq_one_iff {p : ℕ} (hp : p.Prime) : Ipair p = 1 ↔ p = 2 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_lt (Ipair_prime_lt_one hp hne))
  · rintro rfl
    exact Ipair_val_2

/-- **Breaking the one-bit cap forces the cyclic order to be composite.** -/
theorem above_cap_imp_not_prime {n : ℕ} (h : 1 < Ipair n) : ¬ n.Prime := by
  intro hn
  rcases eq_or_ne n 2 with rfl | hne
  · rw [Ipair_val_2] at h
    exact lt_irrefl 1 h
  · exact absurd h (not_lt.2 (Ipair_prime_lt_one hn hne).le)

/-- The prime channel decays: an explicit envelope `Ipair p ≤ (log₂ p + 3p)/p²`
for every prime `p`, so the prime-order channel tends to `0`. -/
theorem Ipair_prime_le_envelope {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Ipair p ≤ (Real.logb 2 (p : ℝ) + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have h := hp.two_le
    rcases eq_or_lt_of_le h with h' | h'
    · exact absurd h'.symm hp2
    · omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  set L := Real.logb 2 (p : ℝ) with hL
  set L1 := Real.logb 2 ((p : ℝ) - 1) with hL1
  set L2 := Real.logb 2 ((p : ℝ) - 2) with hL2
  set A := ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 with hA
  set B := ((p : ℝ) - 1) * ((p : ℝ) - 2) / (p : ℝ) ^ 2 with hB
  have hkey : L - L1 ≤ 1 / (((p : ℝ) - 1) * Real.log 2) := by
    have h := logb_sub_logb_le (x := (p : ℝ) - 1) (by linarith)
    have e : (p : ℝ) - 1 + 1 = (p : ℝ) := by ring
    rw [e] at h
    exact h
  have hApos : 0 ≤ A := by
    rw [hA]; apply div_nonneg _ (by positivity); nlinarith
  have hBpos : 0 ≤ B := by
    rw [hB]; apply div_nonneg _ (by positivity); nlinarith
  have hL2le : L2 ≤ L := by
    rw [hL2, hL]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hdecomp : Ipair p = L * (1 - A + B) + A * (L - L1) - B * (L - L2) := by
    rw [Ipair_prime hp, hA, hB, hL, hL1, hL2]
    field_simp
    ring
  have hcoeff : 1 - A + B = 1 / (p : ℝ) ^ 2 := by
    rw [hA, hB]; field_simp; ring
  have hne1' : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hne2' : (p : ℝ) ≠ 0 := by linarith
  have hne3' : Real.log 2 ≠ 0 := by linarith
  have hstep1 : A * (L - L1) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    calc A * (L - L1) ≤ A * (1 / (((p : ℝ) - 1) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hkey hApos
      _ = (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
          rw [hA]; field_simp
  have hstep2 : 0 ≤ B * (L - L2) := mul_nonneg hBpos (by linarith)
  have hbound : (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) ≤ 3 * (p : ℝ) / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcube : (0 : ℝ) < (p : ℝ) ^ 3 := by positivity
    have hmul : (p : ℝ) ^ 3 * 0.6931471803 < (p : ℝ) ^ 3 * Real.log 2 :=
      mul_lt_mul_of_pos_left hlog2 hcube
    nlinarith [hmul, hcube]
  have hcollect : L / (p : ℝ) ^ 2 + 3 * (p : ℝ) / (p : ℝ) ^ 2
      = (L + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by
    field_simp
  have hLdiv : L * (1 / (p : ℝ) ^ 2) = L / (p : ℝ) ^ 2 := by ring
  rw [hdecomp, hcoeff]
  linarith [hstep1, hstep2, hbound, hcollect, hLdiv]

/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/

/-- The general prime formula at `p = 3` reproduces the enumerated value
`Ipair 3 = log₂ 3 - 10/9`. -/
theorem Ipair_prime_three : Ipair 3 = (-10/9 : ℝ) + Real.logb 2 3 := by
  have h := Ipair_prime (p := 3) (by norm_num)
  norm_num at h
  rw [h]
  ring

/-- The general prime formula at `p = 5` reproduces the enumerated value. -/
theorem Ipair_prime_five :
    Ipair 5 = (-72/25 : ℝ) + (12/25 : ℝ) * Real.logb 2 3 + Real.logb 2 5 := by
  have h := Ipair_prime (p := 5) (by norm_num)
  norm_num [lb_4] at h
  rw [h]
  ring

end CyclicTypeChannel
-- ==== upstream: Packages/Catalog/NumberTheory/CyclicTypeChannelOdd.lean ====
/-
# Odd cyclic orders above the one-bit cap

The exact-value files show the type-pair channel `Ipair n` breaking the one-bit
binary-fork cap at `n = 4, 6, 8, 10, 12, 16`, and staying below it at the odd
orders `3, 5, 9, 15` (`odd_orders_below_cap`).  That coincidence suggested that
the order-two element of the cyclic group is what pushes the channel above the
cap.  This file **refutes** that reading:

`one_lt_Ipair_odd_order` exhibits an explicit **odd** cyclic order

  `M = 9 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 = 300840735195`

with `1 < Ipair M`.  So the cap is broken by odd orders too; evenness is not the
mechanism.  What *is* the mechanism is CRT additivity (`Ipair_mul_of_coprime`)
together with the fact that every prime-order channel is strictly positive: the
channel of a squarefree-ish odd order is a *sum* of small positive prime
contributions.  The accumulation is *tight*: the prime-order values decay like
`Ipair p ≈ (log₂ p + 2/ln 2)/p²`, so the total over all odd prime powers
converges (numerically to `≈ 1.084`), and the ten primary parts used here
already give `1.0052…` — no odd order can exceed `1.09`, and only a long tail of
primes gets past `1` at all.

The proof is a chain of three ingredients, all already formal:

* `Ipair_prime` — the closed form for a prime cyclic order;
* `Ipair_val_9` — the exact value of the prime-power order `9`;
* `Ipair_mul_of_coprime` — CRT additivity.

Each prime contribution is bounded below by an explicit rational number obtained
from integer inequalities `2 ^ a ≤ x ^ 4096` and `x ^ 4096 ≤ 2 ^ c`
(`logb_ge_of_pow_le`, `logb_le_of_le_pow`); summing the ten bounds gives
`Ipair M ≥ 1.0052… > 1`.
-/

namespace CyclicTypeChannel

set_option exponentiation.threshold 100000

/-! ## 1. Rational bounds for binary logarithms -/

/-- If `2 ^ a ≤ x ^ b` then `a / b ≤ log₂ x`: a rational lower bound for a binary
logarithm, certified by an integer inequality. -/
lemma logb_ge_of_pow_le {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : (2 : ℝ) ^ a ≤ x ^ b) : (a : ℝ) / (b : ℝ) ≤ Real.logb 2 x := by
  have h1 : Real.logb 2 ((2 : ℝ) ^ a) ≤ Real.logb 2 (x ^ b) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  nlinarith [h1]

/-- If `x ^ b ≤ 2 ^ a` then `log₂ x ≤ a / b`. -/
lemma logb_le_of_le_pow {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : x ^ b ≤ (2 : ℝ) ^ a) : Real.logb 2 x ≤ (a : ℝ) / (b : ℝ) := by
  have h1 : Real.logb 2 (x ^ b) ≤ Real.logb 2 ((2 : ℝ) ^ a) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  nlinarith [h1]

/-! ## 2. Explicit rational lower bounds for the odd prime-order channels

Each bound is the closed form `Ipair_prime` evaluated with the two-sided
rational bounds of Section 1 at denominator `4096`. -/

/-- A rational lower bound for the prime-power value `Ipair 9 = -100/81 + (10/9) log₂ 3`. -/
lemma Ipair_lb_nine : (21835 / 41472 : ℝ) ≤ Ipair 9 := by
  have h3 : ((6492 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 3 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h3
  rw [Ipair_val_9]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 5`. -/
lemma Ipair_lb_five : (10371 / 51200 : ℝ) ≤ Ipair 5 := by
  have h := Ipair_prime (p := 5) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((9510 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 5 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 4 ≤ ((8192 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((6492 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 3 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 7`. -/
lemma Ipair_lb_seven : (2845 / 25088 : ℝ) ≤ Ipair 7 := by
  have h := Ipair_prime (p := 7) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((11498 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 7 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 6 ≤ ((10589 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((9510 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 5 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 11`. -/
lemma Ipair_lb_eleven : (25539 / 495616 : ℝ) ≤ Ipair 11 := by
  have h := Ipair_prime (p := 11) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((14169 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 11 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 10 ≤ ((13607 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((12984 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 9 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 13`. -/
lemma Ipair_lb_thirteen : (26341 / 692224 : ℝ) ≤ Ipair 13 := by
  have h := Ipair_prime (p := 13) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((15157 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 13 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 12 ≤ ((14685 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((14169 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 11 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 17`. -/
lemma Ipair_lb_seventeen : (14083 / 591872 : ℝ) ≤ Ipair 17 := by
  have h := Ipair_prime (p := 17) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((16742 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 17 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 16 ≤ ((16384 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((16002 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 15 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 19`. -/
lemma Ipair_lb_nineteen : (28145 / 1478656 : ℝ) ≤ Ipair 19 := by
  have h := Ipair_prime (p := 19) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((17399 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 19 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 18 ≤ ((17081 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((16742 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 17 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 23`. -/
lemma Ipair_lb_twentythree : (3669 / 270848 : ℝ) ≤ Ipair 23 := by
  have h := Ipair_prime (p := 23) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((18528 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 23 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 22 ≤ ((18266 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((17990 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 21 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 29`. -/
lemma Ipair_lb_twentynine : (15619 / 1722368 : ℝ) ≤ Ipair 29 := by
  have h := Ipair_prime (p := 29) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((19898 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 29 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 28 ≤ ((19691 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((19476 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 27 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-- A rational lower bound for the prime-order value `Ipair 31`. -/
lemma Ipair_lb_thirtyone : (15351 / 1968128 : ℝ) ≤ Ipair 31 := by
  have h := Ipair_prime (p := 31) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((20292 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 31 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 30 ≤ ((20099 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((19898 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 29 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith

/-! ## 3. An odd cyclic order above the one-bit cap -/

/-- **An odd cyclic order strictly above the one-bit binary-fork cap.**

`M = 9 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 = 300840735195`
is odd and satisfies `Ipair M > 1`.  Together with `odd_orders_below_cap` (all
small odd orders are below the cap) this shows the cap is broken by accumulating
enough odd primary parts, not by the presence of an order-two element. -/
theorem one_lt_Ipair_odd_order : 1 < Ipair 300840735195 := by
  have e45 : Ipair 45 = Ipair 9 + Ipair 5 := by
    rw [show (45 : ℕ) = 9 * 5 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e315 : Ipair 315 = Ipair 45 + Ipair 7 := by
    rw [show (315 : ℕ) = 45 * 7 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e3465 : Ipair 3465 = Ipair 315 + Ipair 11 := by
    rw [show (3465 : ℕ) = 315 * 11 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e45045 : Ipair 45045 = Ipair 3465 + Ipair 13 := by
    rw [show (45045 : ℕ) = 3465 * 13 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e765765 : Ipair 765765 = Ipair 45045 + Ipair 17 := by
    rw [show (765765 : ℕ) = 45045 * 17 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e14549535 : Ipair 14549535 = Ipair 765765 + Ipair 19 := by
    rw [show (14549535 : ℕ) = 765765 * 19 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e334639305 : Ipair 334639305 = Ipair 14549535 + Ipair 23 := by
    rw [show (334639305 : ℕ) = 14549535 * 23 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e9704539845 : Ipair 9704539845 = Ipair 334639305 + Ipair 29 := by
    rw [show (9704539845 : ℕ) = 334639305 * 29 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have e300840735195 : Ipair 300840735195 = Ipair 9704539845 + Ipair 31 := by
    rw [show (300840735195 : ℕ) = 9704539845 * 31 from by norm_num]
    exact Ipair_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have b9 := Ipair_lb_nine
  have bfive := Ipair_lb_five
  have bseven := Ipair_lb_seven
  have beleven := Ipair_lb_eleven
  have bthirteen := Ipair_lb_thirteen
  have bseventeen := Ipair_lb_seventeen
  have bnineteen := Ipair_lb_nineteen
  have btwentythree := Ipair_lb_twentythree
  have btwentynine := Ipair_lb_twentynine
  have bthirtyone := Ipair_lb_thirtyone
  rw [e300840735195, e9704539845, e334639305, e14549535, e765765, e45045, e3465, e315, e45]
  linarith

/-- The above-cap phenomenon does not need an even cyclic order. -/
theorem exists_odd_order_above_cap : ∃ n : ℕ, Odd n ∧ 1 < Ipair n :=
  ⟨300840735195, Nat.odd_iff.2 (by norm_num), one_lt_Ipair_odd_order⟩

/-- The witness is composite with ten primary parts, consistent with
`above_cap_imp_not_prime`: no prime order can break the cap. -/
theorem odd_above_cap_not_prime : ¬ (300840735195 : ℕ).Prime :=
  above_cap_imp_not_prime one_lt_Ipair_odd_order

end CyclicTypeChannel
section
open CyclicTypeChannel

theorem solution  :
    (15351 / 1968128 : ℝ) ≤ Ipair 31 := by
  first
  | exact CyclicTypeChannel.Ipair_lb_thirtyone
  | exact CyclicTypeChannel.Ipair_lb_thirtyone
  | exact @CyclicTypeChannel.Ipair_lb_thirtyone
  | apply CyclicTypeChannel.Ipair_lb_thirtyone
  | exact CyclicTypeChannel.Ipair_lb_thirtyone ..


end
