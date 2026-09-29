-- Prove2me | solution 1 for MetricTSP.support_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-25T05:43:01.141931+00:00
-- url     : https://prove2.me/submissions/825012c7-fcc9-4c18-a394-742d7dbb6509

import Mathlib
import Definitions.Def_MetricTSP_model

set_option maxHeartbeats 1000000

namespace MetricTSP

variable {n : ℕ}

/-! ### Alternating walk matrices

For a walk `h : ℕ → Fin n` of length `m` we form the integer matrix
`zW m h` that places sign `(-1)^k` on the `k`-th step (symmetrized).
Its row sums telescope to a boundary term, so a closed even walk gives a
degree-balanced matrix; an edge traversed an odd number of times receives
an odd, hence nonzero, entry. -/

/-- Symmetrized indicator of the `k`-th step of the walk `h`. -/
def stepInd (h : ℕ → Fin n) (k : ℕ) (u v : Fin n) : ℤ :=
  (if h k = u ∧ h (k + 1) = v then 1 else 0)
    + (if h k = v ∧ h (k + 1) = u then 1 else 0)

/-- The alternating-sign walk matrix. -/
def zW (m : ℕ) (h : ℕ → Fin n) (u v : Fin n) : ℤ :=
  ∑ k ∈ Finset.range m, (-1) ^ k * stepInd h k u v

lemma stepInd_symm (h : ℕ → Fin n) (k : ℕ) (u v : Fin n) :
    stepInd h k u v = stepInd h k v u := by
  unfold stepInd
  ring

lemma zW_symm (m : ℕ) (h : ℕ → Fin n) (u v : Fin n) :
    zW m h u v = zW m h v u :=
  Finset.sum_congr rfl (fun k _ => by rw [stepInd_symm])

lemma zW_diag (m : ℕ) (h : ℕ → Fin n) (hne : ∀ k < m, h k ≠ h (k + 1))
    (v : Fin n) : zW m h v v = 0 := by
  refine Finset.sum_eq_zero (fun k hk => ?_)
  unfold stepInd
  rw [if_neg (fun hh => hne k (Finset.mem_range.mp hk) (hh.1.trans hh.2.symm))]
  ring

lemma zW_supp (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (m : ℕ) (h : ℕ → Fin n) (hadj : ∀ k < m, y (h k) (h (k + 1)) ≠ 0)
    (u v : Fin n) (hz : zW m h u v ≠ 0) : y u v ≠ 0 := by
  by_contra h0
  apply hz
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  unfold stepInd
  rw [if_neg (fun hh => hadj k hk' (by rw [hh.1, hh.2]; exact h0)),
    if_neg (fun hh => hadj k hk' (by rw [hh.1, hh.2, hsym v u]; exact h0))]
  ring

/-- Row sums of a walk matrix telescope to the boundary. -/
lemma zW_row (m : ℕ) (h : ℕ → Fin n) (hstep : ∀ k < m, h k ≠ h (k + 1))
    (v : Fin n) :
    ∑ u, zW m h v u
      = (if h 0 = v then 1 else 0) - (-1) ^ m * (if h m = v then 1 else 0) := by
  induction m with
  | zero =>
    simp only [zW, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero]
    ring
  | succ m ih =>
    have hstep' : ∀ k < m, h k ≠ h (k + 1) := fun k hk => hstep k (by omega)
    have h1 : ∑ u, zW (m + 1) h v u
        = ∑ u, zW m h v u + (-1) ^ m * ∑ u, stepInd h m v u := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      unfold zW
      rw [Finset.sum_range_succ]
    have h2 : ∑ u, stepInd h m v u
        = (if h m = v then 1 else 0) + (if h (m + 1) = v then 1 else 0) := by
      unfold stepInd
      rw [Finset.sum_add_distrib]
      congr 1
      · by_cases hmv : h m = v
        · rw [if_pos hmv]
          rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => by
            rw [show (if h m = v ∧ h (m + 1) = u then (1:ℤ) else 0)
              = (if h (m + 1) = u then 1 else 0) from by
                by_cases hu : h (m + 1) = u
                · rw [if_pos ⟨hmv, hu⟩, if_pos hu]
                · rw [if_neg (fun hh => hu hh.2), if_neg hu]])]
          rw [Finset.sum_ite_eq Finset.univ (h (m + 1)) (fun _ => (1:ℤ)),
            if_pos (Finset.mem_univ _)]
        · rw [if_neg hmv]
          exact Finset.sum_eq_zero (fun u _ => if_neg (fun hh => hmv hh.1))
      · by_cases hmv : h (m + 1) = v
        · rw [if_pos hmv]
          rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => by
            rw [show (if h m = u ∧ h (m + 1) = v then (1:ℤ) else 0)
              = (if h m = u then 1 else 0) from by
                by_cases hu : h m = u
                · rw [if_pos ⟨hu, hmv⟩, if_pos hu]
                · rw [if_neg (fun hh => hu hh.1), if_neg hu]])]
          rw [Finset.sum_ite_eq Finset.univ (h m) (fun _ => (1:ℤ)),
            if_pos (Finset.mem_univ _)]
        · rw [if_neg hmv]
          exact Finset.sum_eq_zero (fun u _ => if_neg (fun hh => hmv hh.2))
    rw [h1, ih hstep', h2]
    ring

/-- Number of times the walk `h` traverses the unordered pair `{u, v}`. -/
def cntE (m : ℕ) (h : ℕ → Fin n) (u v : Fin n) : ℕ :=
  ((Finset.range m).filter
    (fun k => (h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u))).card

lemma stepInd_eq_ite (h : ℕ → Fin n) (k : ℕ) {u v : Fin n} (huv : u ≠ v) :
    stepInd h k u v
      = if (h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u)
        then 1 else 0 := by
  unfold stepInd
  by_cases h1 : h k = u ∧ h (k + 1) = v
  · rw [if_pos h1, if_neg (fun h2 => huv (h1.1.symm.trans h2.1)),
      if_pos (Or.inl h1)]
    ring
  · rw [if_neg h1]
    by_cases h2 : h k = v ∧ h (k + 1) = u
    · rw [if_pos h2, if_pos (Or.inr h2)]
      ring
    · rw [if_neg h2, if_neg (fun hh => hh.elim h1 h2)]
      ring

lemma parity_sum_neg_one_pow (F : Finset ℕ) :
    Even ((∑ k ∈ F, (-1 : ℤ) ^ k) - F.card) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    obtain ⟨t, ht⟩ := ih
    rcases Int.even_or_odd a with he | ho
    · rw [Even.neg_one_pow (by exact_mod_cast he)]
      exact ⟨t, by push_cast at ht ⊢; linarith⟩
    · rw [Odd.neg_one_pow (by exact_mod_cast ho)]
      exact ⟨t - 1, by push_cast at ht ⊢; linarith⟩

/-- A pair traversed an odd number of times has a nonzero entry. -/
lemma zW_ne_zero_of_odd_cnt (m : ℕ) (h : ℕ → Fin n) {u v : Fin n}
    (huv : u ≠ v) (hodd : Odd (cntE m h u v)) : zW m h u v ≠ 0 := by
  classical
  have hz : zW m h u v = ∑ k ∈ (Finset.range m).filter
      (fun k => (h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u)),
      (-1 : ℤ) ^ k := by
    unfold zW
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [stepInd_eq_ite h k huv]
    by_cases hk : (h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u)
    · rw [if_pos hk, if_pos hk]
      ring
    · rw [if_neg hk, if_neg hk]
      ring
  intro h0
  rw [hz] at h0
  obtain ⟨t, ht⟩ := parity_sum_neg_one_pow ((Finset.range m).filter
    (fun k => (h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u)))
  rw [h0] at ht
  unfold cntE at hodd
  obtain ⟨r, hr⟩ := hodd
  omega

/-- A pair never traversed has a zero entry. -/
lemma zW_eq_zero_of_avoid (m : ℕ) (h : ℕ → Fin n) (u v : Fin n)
    (havoid : ∀ k < m,
      ¬((h k = u ∧ h (k + 1) = v) ∨ (h k = v ∧ h (k + 1) = u))) :
    zW m h u v = 0 := by
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  unfold stepInd
  rw [if_neg (fun hh => havoid k hk' (Or.inl hh)),
    if_neg (fun hh => havoid k hk' (Or.inr hh))]
  ring

/-- On a walk injective on `[0, m]`, each traversed pair is traversed once. -/
lemma cnt_one_of_path (m : ℕ) (h : ℕ → Fin n)
    (hinj : ∀ k ≤ m, ∀ l ≤ m, h k = h l → k = l)
    (k₀ : ℕ) (hk₀ : k₀ < m) : cntE m h (h k₀) (h (k₀ + 1)) = 1 := by
  classical
  unfold cntE
  rw [show ((Finset.range m).filter
      (fun k => (h k = h k₀ ∧ h (k + 1) = h (k₀ + 1))
        ∨ (h k = h (k₀ + 1) ∧ h (k + 1) = h k₀))) = {k₀} from ?_]
  · exact Finset.card_singleton k₀
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hkm, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact hinj k (by omega) k₀ (by omega) h1
      · have e1 : k = k₀ + 1 := hinj k (by omega) (k₀ + 1) (by omega) h1
        have e2 : k + 1 = k₀ := hinj (k + 1) (by omega) k₀ (by omega) h2
        omega
    · intro hk
      subst hk
      exact ⟨hk₀, Or.inl ⟨rfl, rfl⟩⟩

/-- On a simple cycle (injective on `[0, m)`, closed at `m ≥ 3`),
each traversed pair is traversed once. -/
lemma cnt_one_of_cycle (m : ℕ) (h : ℕ → Fin n) (hm : 3 ≤ m)
    (hclose : h m = h 0)
    (hinj : ∀ k < m, ∀ l < m, h k = h l → k = l)
    (k₀ : ℕ) (hk₀ : k₀ < m) : cntE m h (h k₀) (h (k₀ + 1)) = 1 := by
  classical
  have hmod : ∀ k, k ≤ m → h k = h (k % m) := by
    intro k hk
    rcases Nat.lt_or_ge k m with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · have : k = m := by omega
      rw [this, hclose, Nat.mod_self]
  unfold cntE
  rw [show ((Finset.range m).filter
      (fun k => (h k = h k₀ ∧ h (k + 1) = h (k₀ + 1))
        ∨ (h k = h (k₀ + 1) ∧ h (k + 1) = h k₀))) = {k₀} from ?_]
  · exact Finset.card_singleton k₀
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hkm, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact hinj k hkm k₀ hk₀ h1
      · -- backwards traversal: k ≡ k₀ + 1 and k + 1 ≡ k₀ (mod m), so m ∣ 2
        have e1 : k = (k₀ + 1) % m := by
          refine hinj k hkm ((k₀ + 1) % m) (Nat.mod_lt _ (by omega)) ?_
          rw [h1, hmod (k₀ + 1) (by omega)]
        have e2 : (k + 1) % m = k₀ := by
          refine hinj ((k + 1) % m) (Nat.mod_lt _ (by omega)) k₀ hk₀ ?_
          rw [← hmod (k + 1) (by omega), h2]
        -- from e1, e2: (k₀ + 2) % m = k₀, impossible for m ≥ 3
        exfalso
        rcases Nat.lt_or_ge (k₀ + 1) m with hc | hc
        · rw [Nat.mod_eq_of_lt hc] at e1
          subst e1
          rcases Nat.lt_or_ge (k₀ + 2) m with hd | hd
          · rw [Nat.mod_eq_of_lt hd] at e2
            omega
          · have : k₀ + 2 = m := by omega
            rw [show k₀ + 1 + 1 = m from by omega, Nat.mod_self] at e2
            omega
        · have : k₀ + 1 = m := by omega
          rw [this, Nat.mod_self] at e1
          subst e1
          rw [Nat.mod_eq_of_lt (by omega)] at e2
          omega
    · intro hk
      subst hk
      exact ⟨hk₀, Or.inl ⟨rfl, rfl⟩⟩

/-! ### Non-backtracking walks in the support graph -/

/-- Two-step state of the deterministic walk driven by a successor map `s`. -/
def walkP (s : Fin n → Fin n → Fin n) (a b : Fin n) : ℕ → Fin n × Fin n :=
  fun k => Nat.rec (a, b) (fun _ p => (p.2, s p.2 p.1)) k

/-- The walk itself. -/
def wk (s : Fin n → Fin n → Fin n) (a b : Fin n) (k : ℕ) : Fin n :=
  (walkP s a b k).1

lemma wk_zero (s : Fin n → Fin n → Fin n) (a b : Fin n) : wk s a b 0 = a := rfl

lemma wk_one (s : Fin n → Fin n → Fin n) (a b : Fin n) : wk s a b 1 = b := rfl

lemma wk_succ2 (s : Fin n → Fin n → Fin n) (a b : Fin n) (k : ℕ) :
    wk s a b (k + 2) = s (wk s a b (k + 1)) (wk s a b k) := rfl

section WalkSpec

variable {W : Finset (Fin n)} {y : Fin n → Fin n → ℝ}
  {s : Fin n → Fin n → Fin n}

/-- The fundamental walk invariant: every step is a support edge, and the
walk never immediately backtracks. -/
lemma wk_spec (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hs : ∀ v p, v ∈ W → y v (s v p) ≠ 0 ∧ s v p ≠ p)
    {a b : Fin n} (hab : y a b ≠ 0) :
    ∀ k, y (wk s a b k) (wk s a b (k + 1)) ≠ 0
      ∧ wk s a b (k + 2) ≠ wk s a b k := by
  intro k
  induction k with
  | zero =>
    constructor
    · rw [wk_zero, wk_one]
      exact hab
    · rw [wk_succ2, wk_one, wk_zero]
      exact (hs b a (hsupp a b hab).2).2
  | succ k ih =>
    have hmem : wk s a b (k + 1) ∈ W := (hsupp _ _ ih.1).2
    have hadj : y (wk s a b (k + 1)) (wk s a b (k + 2)) ≠ 0 := by
      rw [wk_succ2]
      exact (hs (wk s a b (k + 1)) (wk s a b k) hmem).1
    refine ⟨hadj, ?_⟩
    have hmem2 : wk s a b (k + 2) ∈ W := (hsupp _ _ hadj).2
    rw [show k + 1 + 2 = k + 2 + 1 from rfl, wk_succ2]
    exact (hs (wk s a b (k + 2)) (wk s a b (k + 1)) hmem2).2

/-- Any walk in a finite graph repeats a vertex. -/
lemma wk_repeat (hn : 0 < n) (g : ℕ → Fin n) :
    ∃ j, ∃ i, i < j ∧ g i = g j := by
  classical
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (n + 1)) (t := Finset.univ)
      (by rw [Finset.card_range, Finset.card_univ, Fintype.card_fin]; omega)
      (fun i _ => Finset.mem_univ (g i))
  rcases Nat.lt_or_ge i j with h | h
  · exact ⟨j, i, h, heq⟩
  · have : j < i := by omega
    exact ⟨i, j, this, heq.symm⟩

/-- Extraction of a simple cycle from a non-backtracking support walk. -/
lemma exists_cycle (hn : 0 < n)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdiag : ∀ v, y v v = 0)
    (hs : ∀ v p, v ∈ W → y v (s v p) ≠ 0 ∧ s v p ≠ p)
    {a b : Fin n} (hab : y a b ≠ 0) :
    ∃ (m : ℕ) (h₁ : ℕ → Fin n), 3 ≤ m ∧ h₁ m = h₁ 0
      ∧ (∀ t, y (h₁ t) (h₁ (t + 1)) ≠ 0)
      ∧ (∀ t t', t < m → t' < m → h₁ t = h₁ t' → t = t') := by
  classical
  set g := wk s a b with hg
  have hspec := wk_spec hsupp hs hab
  rw [← hg] at hspec
  have hrep := wk_repeat hn g
  set J := Nat.find hrep with hJ
  obtain ⟨i₀, hi₀, heq⟩ := Nat.find_spec hrep
  have hmin : ∀ j, j < J → ¬∃ i, i < j ∧ g i = g j :=
    fun j hj => Nat.find_min hrep hj
  have hinjJ : ∀ k l, k < J → l < J → g k = g l → k = l := by
    intro k l hk hl hkl
    rcases Nat.lt_trichotomy k l with h | h | h
    · exact absurd ⟨k, h, hkl⟩ (hmin l hl)
    · exact h
    · exact absurd ⟨l, h, hkl.symm⟩ (hmin k hk)
  set m := J - i₀ with hm
  refine ⟨m, fun t => g (i₀ + t), ?_, ?_, ?_, ?_⟩
  · -- 3 ≤ m
    have h1 : 1 ≤ m := by omega
    have h2 : m ≠ 1 := by
      intro h
      have : g i₀ = g (i₀ + 1) := by
        rw [show i₀ + 1 = J from by omega]
        exact heq
      have hadj := (hspec i₀).1
      rw [← this] at hadj
      exact hadj (hdiag (g i₀))
    have h3 : m ≠ 2 := by
      intro h
      have : g i₀ = g (i₀ + 2) := by
        rw [show i₀ + 2 = J from by omega]
        exact heq
      exact (hspec i₀).2 this.symm
    omega
  · show g (i₀ + m) = g (i₀ + 0)
    rw [show i₀ + m = J from by omega, Nat.add_zero]
    exact heq.symm
  · intro t
    exact (hspec (i₀ + t)).1
  · intro t t' ht ht' htt
    have := hinjJ (i₀ + t) (i₀ + t') (by omega) (by omega) htt
    omega

end WalkSpec

/-! ### Packaging and parity helpers -/

/-- Package an integer perturbation matrix into the real statement. -/
lemma z_package (y : Fin n → Fin n → ℝ) (zI : Fin n → Fin n → ℤ)
    (e₁ e₂ : Fin n) (hne : zI e₁ e₂ ≠ 0)
    (hsymI : ∀ u v, zI u v = zI v u) (hdiagI : ∀ v, zI v v = 0)
    (hsuppI : ∀ u v, zI u v ≠ 0 → y u v ≠ 0)
    (hrowI : ∀ v, ∑ u, zI v u = 0) :
    ∃ z : Fin n → Fin n → ℝ, z ≠ 0 ∧ (∀ u v, z u v = z v u) ∧
      (∀ v, z v v = 0) ∧ (∀ u v, z u v ≠ 0 → y u v ≠ 0) ∧
      (∀ v, ∑ u, z v u = 0) := by
  refine ⟨fun u v => ((zI u v : ℤ) : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrFun (congrFun h0 e₁) e₂
    simp only [Pi.zero_apply] at h1
    exact hne (Int.cast_eq_zero.mp h1)
  · intro u v
    show ((zI u v : ℤ) : ℝ) = ((zI v u : ℤ) : ℝ)
    exact_mod_cast hsymI u v
  · intro v
    show ((zI v v : ℤ) : ℝ) = 0
    rw [hdiagI v]
    exact Int.cast_zero
  · intro u v h0
    exact hsuppI u v (fun hz => h0 (by
      show ((zI u v : ℤ) : ℝ) = 0
      rw [hz]
      exact Int.cast_zero))
  · intro v
    show ∑ u, ((zI v u : ℤ) : ℝ) = 0
    rw [← Int.cast_sum, hrowI v, Int.cast_zero]

lemma neg_one_pow_cases (k : ℕ) : ((-1 : ℤ) ^ k = 1) ∨ ((-1 : ℤ) ^ k = -1) := by
  rcases Nat.even_or_odd k with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

/-- A shift below the modulus that fixes a residue must be zero. -/
lemma mod_shift_inj {m a d : ℕ} (hm : 0 < m) (hd : d < m)
    (h : (a + d) % m = a % m) : d = 0 := by
  rw [Nat.add_mod] at h
  set r := a % m with hr
  have hrm : r < m := Nat.mod_lt _ hm
  rw [Nat.mod_eq_of_lt hd] at h
  rcases Nat.lt_or_ge (r + d) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    omega
  · have h2 : (r + d) % m = r + d - m := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h
    omega

/-- The step successor of a residue: `(a+1) % m` in terms of `a % m`. -/
lemma mod_succ_eq (m a : ℕ) : (a + 1) % m = (a % m + 1) % m := by
  rw [Nat.mod_add_mod]

/-! ### The three perturbation constructions -/

section Constructions

variable {y : Fin n → Fin n → ℝ}

/-- The perturbation target predicate. -/
def IsPerturb (y : Fin n → Fin n → ℝ) (z : Fin n → Fin n → ℝ) : Prop :=
  z ≠ 0 ∧ (∀ u v, z u v = z v u) ∧ (∀ v, z v v = 0) ∧
    (∀ u v, z u v ≠ 0 → y u v ≠ 0) ∧ (∀ v, ∑ u, z v u = 0)

/-- An even simple cycle in the support yields a perturbation. -/
lemma z_of_even_cycle (hsym : ∀ u v, y u v = y v u) (hdiag : ∀ v, y v v = 0)
    (m : ℕ) (h₁ : ℕ → Fin n) (hm3 : 3 ≤ m) (hme : Even m)
    (hcl : h₁ m = h₁ 0)
    (hadj : ∀ t, y (h₁ t) (h₁ (t + 1)) ≠ 0)
    (hinj : ∀ t t', t < m → t' < m → h₁ t = h₁ t' → t = t') :
    ∃ z, IsPerturb y z := by
  have hstep : ∀ t, h₁ t ≠ h₁ (t + 1) :=
    fun t he => hadj t (by rw [he]; exact hdiag _)
  obtain ⟨z, hz⟩ := z_package y (zW m h₁) (h₁ 0) (h₁ 1)
    (zW_ne_zero_of_odd_cnt m h₁ (hstep 0)
      (by rw [cnt_one_of_cycle m h₁ hm3 hcl (fun k hk l hl => hinj k l hk hl) 0 (by omega)]
          exact ⟨0, by norm_num⟩))
    (zW_symm m h₁) (zW_diag m h₁ (fun k _ => hstep k))
    (zW_supp y hsym m h₁ (fun k _ => hadj k))
    (fun v => by
      rw [zW_row m h₁ (fun k _ => hstep k) v, hcl, Even.neg_one_pow hme]
      ring)
  exact ⟨z, hz⟩

/-- Two support paths with common endpoints and lengths of equal parity,
the first injective and the second avoiding the first edge of the first,
yield a perturbation. -/
lemma z_of_two_paths (hsym : ∀ u v, y u v = y v u) (hdiag : ∀ v, y v v = 0)
    (p : ℕ) (hP : ℕ → Fin n) (hp : 0 < p)
    (q : ℕ) (hQ : ℕ → Fin n)
    (hP0 : hP 0 = hQ 0) (hPp : hP p = hQ q)
    (hpar : (-1 : ℤ) ^ p = (-1 : ℤ) ^ q)
    (hadjP : ∀ t < p, y (hP t) (hP (t + 1)) ≠ 0)
    (hadjQ : ∀ t < q, y (hQ t) (hQ (t + 1)) ≠ 0)
    (hinjP : ∀ t, t ≤ p → ∀ t', t' ≤ p → hP t = hP t' → t = t')
    (havoidQ : ∀ k < q, ¬((hQ k = hP 0 ∧ hQ (k + 1) = hP 1)
      ∨ (hQ k = hP 1 ∧ hQ (k + 1) = hP 0))) :
    ∃ z, IsPerturb y z := by
  have hstepP : ∀ t < p, hP t ≠ hP (t + 1) :=
    fun t ht he => hadjP t ht (by rw [he]; exact hdiag _)
  have hstepQ : ∀ t < q, hQ t ≠ hQ (t + 1) :=
    fun t ht he => hadjQ t ht (by rw [he]; exact hdiag _)
  have h1 : cntE p hP (hP 0) (hP 1) = 1 := cnt_one_of_path p hP hinjP 0 hp
  have h2 : zW p hP (hP 0) (hP 1) ≠ 0 :=
    zW_ne_zero_of_odd_cnt p hP (hstepP 0 hp) (by rw [h1]; exact ⟨0, by norm_num⟩)
  have h3 : zW q hQ (hP 0) (hP 1) = 0 := zW_eq_zero_of_avoid q hQ _ _ havoidQ
  obtain ⟨z, hz⟩ := z_package y (fun u v => zW p hP u v - zW q hQ u v)
    (hP 0) (hP 1)
    (by
      show zW p hP (hP 0) (hP 1) - zW q hQ (hP 0) (hP 1) ≠ 0
      rw [h3, sub_zero]
      exact h2)
    (fun u v => by
      show zW p hP u v - zW q hQ u v = zW p hP v u - zW q hQ v u
      rw [zW_symm p hP u v, zW_symm q hQ u v])
    (fun v => by
      show zW p hP v v - zW q hQ v v = 0
      rw [zW_diag p hP hstepP v, zW_diag q hQ hstepQ v]
      ring)
    (fun u v h0 => by
      by_contra hy0
      apply h0
      show zW p hP u v - zW q hQ u v = 0
      have hz1 : zW p hP u v = 0 := by
        by_contra hzc
        exact (zW_supp y hsym p hP hadjP u v hzc) hy0
      have hz2 : zW q hQ u v = 0 := by
        by_contra hzc
        exact (zW_supp y hsym q hQ hadjQ u v hzc) hy0
      rw [hz1, hz2, sub_zero])
    (fun v => by
      show ∑ u, (zW p hP v u - zW q hQ v u) = 0
      rw [Finset.sum_sub_distrib, zW_row p hP hstepP v, zW_row q hQ hstepQ v,
        hP0, hPp, hpar]
      ring)
  exact ⟨z, hz⟩

/-- Two odd cycles joined by a support walk yield a perturbation. -/
lemma z_of_cycles_path (hsym : ∀ u v, y u v = y v u) (hdiag : ∀ v, y v v = 0)
    (m₁ : ℕ) (hA : ℕ → Fin n) (hm₁ : 3 ≤ m₁) (ho₁ : Odd m₁)
    (hclA : hA m₁ = hA 0)
    (hadjA : ∀ t, y (hA t) (hA (t + 1)) ≠ 0)
    (hinjA : ∀ t t', t < m₁ → t' < m₁ → hA t = hA t' → t = t')
    (m₂ : ℕ) (hB : ℕ → Fin n) (ho₂ : Odd m₂) (hclB : hB m₂ = hB 0)
    (hadjB : ∀ t < m₂, y (hB t) (hB (t + 1)) ≠ 0)
    (p : ℕ) (hP : ℕ → Fin n) (hP0 : hP 0 = hA 0) (hPp : hP p = hB 0)
    (hadjP : ∀ t < p, y (hP t) (hP (t + 1)) ≠ 0)
    (havoidB : ∀ k < m₂, ¬((hB k = hA 0 ∧ hB (k + 1) = hA 1)
      ∨ (hB k = hA 1 ∧ hB (k + 1) = hA 0)))
    (havoidP : ∀ k < p, ¬((hP k = hA 0 ∧ hP (k + 1) = hA 1)
      ∨ (hP k = hA 1 ∧ hP (k + 1) = hA 0))) :
    ∃ z, IsPerturb y z := by
  have hstepA : ∀ t, hA t ≠ hA (t + 1) :=
    fun t he => hadjA t (by rw [he]; exact hdiag _)
  have hstepB : ∀ t < m₂, hB t ≠ hB (t + 1) :=
    fun t ht he => hadjB t ht (by rw [he]; exact hdiag _)
  have hstepP : ∀ t < p, hP t ≠ hP (t + 1) :=
    fun t ht he => hadjP t ht (by rw [he]; exact hdiag _)
  have hzA : zW m₁ hA (hA 0) (hA 1) ≠ 0 :=
    zW_ne_zero_of_odd_cnt m₁ hA (hstepA 0)
      (by rw [cnt_one_of_cycle m₁ hA hm₁ hclA (fun k hk l hl => hinjA k l hk hl) 0 (by omega)]
          exact ⟨0, by norm_num⟩)
  have hzB : zW m₂ hB (hA 0) (hA 1) = 0 := zW_eq_zero_of_avoid m₂ hB _ _ havoidB
  have hzP : zW p hP (hA 0) (hA 1) = 0 := zW_eq_zero_of_avoid p hP _ _ havoidP
  obtain ⟨z, hz⟩ := z_package y
    (fun u v => zW m₁ hA u v + (-(-1 : ℤ) ^ p) * zW m₂ hB u v
      - 2 * zW p hP u v)
    (hA 0) (hA 1)
    (by
      show zW m₁ hA (hA 0) (hA 1) + (-(-1 : ℤ) ^ p) * zW m₂ hB (hA 0) (hA 1)
        - 2 * zW p hP (hA 0) (hA 1) ≠ 0
      rw [hzB, hzP, mul_zero, mul_zero, add_zero, sub_zero]
      exact hzA)
    (fun u v => by
      show zW m₁ hA u v + (-(-1 : ℤ) ^ p) * zW m₂ hB u v - 2 * zW p hP u v
        = zW m₁ hA v u + (-(-1 : ℤ) ^ p) * zW m₂ hB v u - 2 * zW p hP v u
      rw [zW_symm m₁ hA u v, zW_symm m₂ hB u v, zW_symm p hP u v])
    (fun v => by
      show zW m₁ hA v v + (-(-1 : ℤ) ^ p) * zW m₂ hB v v - 2 * zW p hP v v = 0
      rw [zW_diag m₁ hA (fun k _ => hstepA k) v, zW_diag m₂ hB hstepB v,
        zW_diag p hP hstepP v]
      ring)
    (fun u v h0 => by
      by_contra hy0
      apply h0
      show zW m₁ hA u v + (-(-1 : ℤ) ^ p) * zW m₂ hB u v
        - 2 * zW p hP u v = 0
      have hz1 : zW m₁ hA u v = 0 := by
        by_contra hzc
        exact (zW_supp y hsym m₁ hA (fun k _ => hadjA k) u v hzc) hy0
      have hz2 : zW m₂ hB u v = 0 := by
        by_contra hzc
        exact (zW_supp y hsym m₂ hB hadjB u v hzc) hy0
      have hz3 : zW p hP u v = 0 := by
        by_contra hzc
        exact (zW_supp y hsym p hP hadjP u v hzc) hy0
      rw [hz1, hz2, hz3]
      ring)
    (fun v => by
      show ∑ u, (zW m₁ hA v u + (-(-1 : ℤ) ^ p) * zW m₂ hB v u
        - 2 * zW p hP v u) = 0
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, zW_row m₁ hA (fun k _ => hstepA k) v,
        zW_row m₂ hB hstepB v, zW_row p hP hstepP v,
        hclA, hclB, hP0, hPp, Odd.neg_one_pow ho₁, Odd.neg_one_pow ho₂]
      ring)
  exact ⟨z, hz⟩

end Constructions

/-! ### The main theorem -/

theorem support_perturbation_thm (W : Finset (Fin n)) (hW : Even W.card)
    (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hfrac : ∀ u v, y u v ≠ 0 → y u v < 1)
    (hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ z, IsPerturb y z := by
  classical
  obtain ⟨w₀, hw₀⟩ := hWn
  have hn : 0 < n := w₀.pos
  -- every vertex of W has two distinct support neighbours
  have htwo : ∀ v ∈ W, ∀ p : Fin n, ∃ u, y v u ≠ 0 ∧ u ≠ p := by
    intro v hv p
    have hd1 := hdeg v hv
    have h1 : ∃ u₁, y v u₁ ≠ 0 := by
      by_contra hno
      push_neg at hno
      rw [Finset.sum_eq_zero (fun u _ => hno u)] at hd1
      norm_num at hd1
    obtain ⟨u₁, hu₁⟩ := h1
    have h2 : ∃ u₂, y v u₂ ≠ 0 ∧ u₂ ≠ u₁ := by
      by_contra hno
      push_neg at hno
      have hsum := Finset.sum_eq_single (s := Finset.univ)
        (f := fun u => y v u) u₁
        (fun u _ hu => by
          by_contra h0
          exact hu (hno u h0))
        (fun h => absurd (Finset.mem_univ u₁) h)
      rw [hsum] at hd1
      exact (ne_of_lt (hfrac v u₁ hu₁)) hd1
    obtain ⟨u₂, hu₂, hne⟩ := h2
    by_cases hp : u₁ = p
    · exact ⟨u₂, hu₂, by rw [← hp]; exact hne⟩
    · exact ⟨u₁, hu₁, hp⟩
  -- a non-backtracking successor function
  have hstot : ∀ v p : Fin n, ∃ u, v ∈ W → (y v u ≠ 0 ∧ u ≠ p) := by
    intro v p
    by_cases hv : v ∈ W
    · obtain ⟨u, h1, h2⟩ := htwo v hv p
      exact ⟨u, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨v, fun h => absurd h hv⟩
  choose s hs using hstot
  -- the first simple cycle
  obtain ⟨b₀, hb₀, -⟩ := htwo w₀ hw₀ w₀
  obtain ⟨m, h₁, hm3, hcl, hadj, hinj⟩ := exists_cycle hn hsupp hdiag hs hb₀
  by_cases hme : Even m
  · exact z_of_even_cycle hsym hdiag m h₁ hm3 hme hcl hadj hinj
  have hmodd : Odd m := Nat.odd_iff.mpr (Nat.not_even_iff.mp hme)
  have hm0 : 0 < m := by omega
  -- a chord vertex, or the odd cycle is a closed component
  by_cases hch : ∃ k₀, k₀ < m ∧ ∃ u₀, y (h₁ k₀) u₀ ≠ 0
      ∧ u₀ ≠ h₁ ((k₀ + 1) % m) ∧ u₀ ≠ h₁ ((k₀ + (m - 1)) % m)
  swap
  · -- no chord: the odd cycle vertex set has zero cut, contradicting `hodd`
    exfalso
    push_neg at hch
    have hio : Set.InjOn h₁ (Finset.range m) := fun t ht t' ht' htt =>
      hinj t t' (Finset.mem_range.mp ht) (Finset.mem_range.mp ht') htt
    set S := (Finset.range m).image h₁ with hSdef
    have hScard : S.card = m := by
      rw [hSdef, Finset.card_image_of_injOn hio, Finset.card_range]
    have hSW : S ⊆ W := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact (hsupp _ _ (hadj t)).1
    have hcut := hodd S hSW (by rw [hScard]; exact hmodd)
    have hzero : ∑ u ∈ S, ∑ v ∈ W \ S, y u v = 0 := by
      refine Finset.sum_eq_zero (fun u hu => Finset.sum_eq_zero (fun v hv => ?_))
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      by_contra h0
      have htm := Finset.mem_range.mp ht
      by_cases h1 : v = h₁ ((t + 1) % m)
      · have hvS : v ∈ S := by
          rw [h1]
          exact Finset.mem_image.mpr
            ⟨(t + 1) % m, Finset.mem_range.mpr (Nat.mod_lt _ hm0), rfl⟩
        exact (Finset.mem_sdiff.mp hv).2 hvS
      · have h2 := hch t htm v h0 h1
        have hvS : v ∈ S := by
          rw [h2]
          exact Finset.mem_image.mpr
            ⟨(t + (m - 1)) % m, Finset.mem_range.mpr (Nat.mod_lt _ hm0), rfl⟩
        exact (Finset.mem_sdiff.mp hv).2 hvS
    rw [hzero] at hcut
    norm_num at hcut
  obtain ⟨k₀, hk₀m, u₀, hu₀, hu₀1, hu₀2⟩ := hch
  -- the rotated cycle anchored at the chord vertex
  obtain ⟨h', hh'⟩ : ∃ f : ℕ → Fin n, ∀ t, f t = h₁ ((k₀ + t) % m) :=
    ⟨_, fun t => rfl⟩
  set x₀ := h₁ k₀ with hx₀def
  have h'0 : h' 0 = x₀ := by
    rw [hh' 0, Nat.add_zero, Nat.mod_eq_of_lt hk₀m]
  have h'cl : h' m = h' 0 := by
    rw [hh' m, hh' 0, Nat.add_mod_right, Nat.add_zero]
  have h'adj : ∀ t, y (h' t) (h' (t + 1)) ≠ 0 := by
    intro t
    rw [hh' t, hh' (t + 1)]
    have hstep2 : (k₀ + (t + 1)) % m = ((k₀ + t) % m + 1) % m := by
      rw [show k₀ + (t + 1) = k₀ + t + 1 from by omega, mod_succ_eq]
    set r := (k₀ + t) % m with hrdef
    have hrm : r < m := Nat.mod_lt _ hm0
    rcases Nat.lt_or_ge (r + 1) m with hlt | hge
    · rw [hstep2, Nat.mod_eq_of_lt hlt]
      exact hadj r
    · have hr1 : r + 1 = m := by omega
      rw [hstep2, hr1, Nat.mod_self]
      have hthis := hadj r
      rw [hr1, hcl] at hthis
      exact hthis
  have h'inj : ∀ t t', t < m → t' < m → h' t = h' t' → t = t' := by
    intro t t' ht ht' htt
    rw [hh' t, hh' t'] at htt
    have h1 := hinj _ _ (Nat.mod_lt _ hm0) (Nat.mod_lt _ hm0) htt
    rcases Nat.le_total t t' with hle | hle
    · have := mod_shift_inj hm0 (show t' - t < m from by omega)
        (by rw [show k₀ + t + (t' - t) = k₀ + t' from by omega]; exact h1.symm)
      omega
    · have := mod_shift_inj hm0 (show t - t' < m from by omega)
        (by rw [show k₀ + t' + (t - t') = k₀ + t from by omega]; exact h1)
      omega
  -- the second walk, from the chord
  have hu₀' : y x₀ u₀ ≠ 0 := hu₀
  set g₂ := wk s x₀ u₀ with hg₂def
  have hspec₂ := wk_spec hsupp hs hu₀'
  rw [← hg₂def] at hspec₂
  have hg₂0 : g₂ 0 = x₀ := rfl
  have hg₂1 : g₂ 1 = u₀ := rfl
  set VC := (Finset.range m).image h₁ with hVCdef
  have hVCall : ∀ t, h' t ∈ VC := by
    intro t
    rw [hh' t, hVCdef]
    exact Finset.mem_image.mpr
      ⟨(k₀ + t) % m, Finset.mem_range.mpr (Nat.mod_lt _ hm0), rfl⟩
  have hVCrep : ∀ x ∈ VC, ∃ d, d < m ∧ h' d = x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨(t + m - k₀) % m, Nat.mod_lt _ hm0, ?_⟩
    rw [hh']
    congr 1
    rw [Nat.add_comm k₀ _, Nat.mod_add_mod,
      show t + m - k₀ + k₀ = t + m from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
  -- the stopping time of the second walk
  have hQex : ∃ j, 1 ≤ j ∧ (g₂ j ∈ VC ∨ ∃ i, i < j ∧ g₂ i = g₂ j) := by
    obtain ⟨j, i, hij, heq⟩ := wk_repeat hn g₂
    exact ⟨j, by omega, Or.inr ⟨i, hij, heq⟩⟩
  set j₂ := Nat.find hQex with hj₂def
  obtain ⟨hj₂1, hdisj⟩ := Nat.find_spec hQex
  have hj₂min : ∀ j, j < j₂ →
      ¬(1 ≤ j ∧ (g₂ j ∈ VC ∨ ∃ i, i < j ∧ g₂ i = g₂ j)) :=
    fun j hj => Nat.find_min hQex hj
  have hg₂mem : ∀ t, 1 ≤ t → t < j₂ → g₂ t ∉ VC :=
    fun t h1 h2 hmem => hj₂min t h2 ⟨h1, Or.inl hmem⟩
  have hg₂inj : ∀ i i', i < j₂ → i' < j₂ → g₂ i = g₂ i' → i = i' := by
    intro i i' hi hi' hii
    rcases Nat.lt_trichotomy i i' with h | h | h
    · exact absurd ⟨by omega, Or.inr ⟨i, h, hii⟩⟩ (hj₂min i' hi')
    · exact h
    · exact absurd ⟨by omega, Or.inr ⟨i', h, hii.symm⟩⟩ (hj₂min i hi)
  have hu₀VC : u₀ ∈ VC → j₂ = 1 := by
    intro hmem
    have h1 : j₂ ≤ 1 := Nat.find_le ⟨le_refl 1, Or.inl (by rw [hg₂1]; exact hmem)⟩
    omega
  have hVCstep : ∀ a, a + 1 ≤ j₂ → g₂ a ∈ VC → g₂ (a + 1) ∈ VC →
      a = 0 ∧ j₂ = 1 := by
    intro a ha hma hma1
    have ha0 : a = 0 := by
      by_contra h0
      exact hg₂mem a (by omega) (by omega) hma
    subst ha0
    refine ⟨rfl, hu₀VC ?_⟩
    rw [← hg₂1]
    exact hma1
  by_cases hselfrep : ∃ i, i < j₂ ∧ g₂ i = g₂ j₂
  · -- the second walk closes on itself: a second cycle `C₂`
    obtain ⟨i, hij, heqA⟩ := hselfrep
    set m₂ := j₂ - i with hm₂def
    have hj₂2 : 2 ≤ j₂ := by
      by_contra h0
      have hj1 : j₂ = 1 := by omega
      have hi0 : i = 0 := by omega
      rw [hi0, hj1, hg₂0, hg₂1] at heqA
      exact hu₀' (by rw [heqA]; exact hdiag u₀)
    have hu₀nVC : u₀ ∉ VC := fun hmem => absurd (hu₀VC hmem) (by omega)
    have hm₂3 : 3 ≤ m₂ := by
      have hm₂1 : 1 ≤ m₂ := by omega
      have hne1 : m₂ ≠ 1 := by
        intro h
        have he : g₂ i = g₂ (i + 1) := by
          rw [show i + 1 = j₂ from by omega]
          exact heqA
        have := (hspec₂ i).1
        rw [← he] at this
        exact this (hdiag (g₂ i))
      have hne2 : m₂ ≠ 2 := by
        intro h
        have he : g₂ (i + 2) = g₂ i := by
          rw [show i + 2 = j₂ from by omega]
          exact heqA.symm
        exact (hspec₂ i).2 he
      omega
    obtain ⟨h₂, hh₂⟩ : ∃ f : ℕ → Fin n, ∀ t, f t = g₂ (i + t) :=
      ⟨_, fun t => rfl⟩
    have h₂cl : h₂ m₂ = h₂ 0 := by
      rw [hh₂ m₂, hh₂ 0, Nat.add_zero, show i + m₂ = j₂ from by omega]
      exact heqA.symm
    have h₂adj : ∀ t, y (h₂ t) (h₂ (t + 1)) ≠ 0 := by
      intro t
      rw [hh₂ t, hh₂ (t + 1), show i + (t + 1) = i + t + 1 from by omega]
      exact (hspec₂ (i + t)).1
    have h₂inj : ∀ t t', t < m₂ → t' < m₂ → h₂ t = h₂ t' → t = t' := by
      intro t t' ht ht' htt
      rw [hh₂ t, hh₂ t'] at htt
      have := hg₂inj (i + t) (i + t') (by omega) (by omega) htt
      omega
    by_cases hm₂e : Even m₂
    · exact z_of_even_cycle hsym hdiag m₂ h₂ hm₂3 hm₂e h₂cl h₂adj h₂inj
    · have hm₂odd : Odd m₂ := Nat.odd_iff.mpr (Nat.not_even_iff.mp hm₂e)
      -- both cycles odd: combine with the connecting path `g₂[0..i]`
      have havB : ∀ k < m₂, ¬((h₂ k = h' 0 ∧ h₂ (k + 1) = h' 1)
          ∨ (h₂ k = h' 1 ∧ h₂ (k + 1) = h' 0)) := by
        intro k hk hmatch
        have hind : g₂ (i + k) ∈ VC ∧ g₂ (i + k + 1) ∈ VC := by
          rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [hh₂ k] at e1
            rw [hh₂ (k + 1), show i + (k + 1) = i + k + 1 from by omega] at e2
            exact ⟨by rw [e1]; exact hVCall 0, by rw [e2]; exact hVCall 1⟩
          · rw [hh₂ k] at e1
            rw [hh₂ (k + 1), show i + (k + 1) = i + k + 1 from by omega] at e2
            exact ⟨by rw [e1]; exact hVCall 1, by rw [e2]; exact hVCall 0⟩
        have := hVCstep (i + k) (by omega) hind.1 hind.2
        omega
      have havP : ∀ k < i, ¬((g₂ k = h' 0 ∧ g₂ (k + 1) = h' 1)
          ∨ (g₂ k = h' 1 ∧ g₂ (k + 1) = h' 0)) := by
        intro k hk hmatch
        have hind : g₂ k ∈ VC ∧ g₂ (k + 1) ∈ VC := by
          rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact ⟨by rw [e1]; exact hVCall 0, by rw [e2]; exact hVCall 1⟩
          · exact ⟨by rw [e1]; exact hVCall 1, by rw [e2]; exact hVCall 0⟩
        have := hVCstep k (by omega) hind.1 hind.2
        omega
      exact z_of_cycles_path hsym hdiag m h' hm3 hmodd h'cl h'adj h'inj
        m₂ h₂ hm₂odd h₂cl (fun t _ => h₂adj t)
        i g₂ (by rw [hg₂0, h'0]) (by rw [hh₂ 0, Nat.add_zero])
        (fun t _ => (hspec₂ t).1) havB havP
  · -- the second walk hits the first cycle: a theta configuration
    push_neg at hselfrep
    have hwVC : g₂ j₂ ∈ VC := by
      rcases hdisj with h | h
      · exact h
      · obtain ⟨i, hi, he⟩ := h
        exact absurd he (hselfrep i hi)
    obtain ⟨d, hdm, hd⟩ := hVCrep _ hwVC
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, h'0] at hd
      exact hselfrep 0 (by omega) (by rw [hg₂0]; exact hd)
    by_cases hpar : (-1 : ℤ) ^ d = (-1 : ℤ) ^ j₂
    · -- arc `h'[0..d]` against the walk `g₂[0..j₂]`
      apply z_of_two_paths hsym hdiag d h' (by omega) j₂ g₂
        (by rw [h'0, hg₂0]) hd hpar (fun t _ => h'adj t)
        (fun t _ => (hspec₂ t).1)
        (fun t ht t' ht' htt => h'inj t t' (by omega) (by omega) htt)
      intro k hk hmatch
      have hind : g₂ k ∈ VC ∧ g₂ (k + 1) ∈ VC := by
        rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨by rw [e1]; exact hVCall 0, by rw [e2]; exact hVCall 1⟩
        · exact ⟨by rw [e1]; exact hVCall 1, by rw [e2]; exact hVCall 0⟩
      obtain ⟨hk0, hj₂1'⟩ := hVCstep k (by omega) hind.1 hind.2
      subst hk0
      rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e2' : g₂ 1 = h' 1 := e2
        rw [hg₂1, hh' 1] at e2'
        exact hu₀1 e2'
      · have e1' : g₂ 0 = h' 1 := e1
        rw [hg₂0, ← h'0] at e1'
        have := h'inj 0 1 (by omega) (by omega) e1'
        omega
    · -- the other arc `h'[d..m]` against the reversed walk
      have hd' : 0 < m - d := by omega
      obtain ⟨h'', hh''⟩ : ∃ f : ℕ → Fin n, ∀ t, f t = h' (d + t) :=
        ⟨_, fun t => rfl⟩
      obtain ⟨gR, hgR⟩ : ∃ f : ℕ → Fin n, ∀ t, f t = g₂ (j₂ - t) :=
        ⟨_, fun t => rfl⟩
      have hkey : (-1 : ℤ) ^ (m - d) * (-1 : ℤ) ^ d = -1 := by
        rw [← pow_add, show m - d + d = m from by omega]
        exact Odd.neg_one_pow hmodd
      have hpar2 : (-1 : ℤ) ^ (m - d) = (-1 : ℤ) ^ j₂ := by
        rcases neg_one_pow_cases d with h | h <;>
          rcases neg_one_pow_cases j₂ with h2 | h2
        · rw [h, h2] at hpar
          exact absurd rfl hpar
        · rw [h] at hkey
          rw [h2]
          linarith
        · rw [h] at hkey
          rw [h2]
          linarith
        · rw [h, h2] at hpar
          exact absurd rfl hpar
      apply z_of_two_paths hsym hdiag (m - d) h'' hd' j₂ gR
        (by rw [hh'' 0, hgR 0, Nat.add_zero, Nat.sub_zero]; exact hd)
        (by rw [hh'' (m - d), hgR j₂, show d + (m - d) = m from by omega,
            Nat.sub_self, h'cl, h'0, hg₂0])
        hpar2
        (by
          intro t _
          rw [hh'' t, hh'' (t + 1), show d + (t + 1) = d + t + 1 from by omega]
          exact h'adj (d + t))
        (by
          intro t ht
          rw [hgR t, hgR (t + 1),
            show j₂ - t = (j₂ - (t + 1)) + 1 from by omega, hsym]
          exact (hspec₂ (j₂ - (t + 1))).1)
        (by
          intro t ht t' ht' htt
          rw [hh'' t, hh'' t'] at htt
          rcases Nat.lt_or_ge (d + t) m with h1 | h1 <;>
            rcases Nat.lt_or_ge (d + t') m with h2 | h2
          · have := h'inj (d + t) (d + t') h1 h2 htt
            omega
          · have hdt' : d + t' = m := by omega
            rw [hdt', h'cl] at htt
            have := h'inj (d + t) 0 h1 (by omega) htt
            omega
          · have hdt : d + t = m := by omega
            rw [hdt, h'cl] at htt
            have := h'inj 0 (d + t') (by omega) h2 htt
            omega
          · omega)
      intro k hk hmatch
      have hind : g₂ (j₂ - k - 1) ∈ VC ∧ g₂ (j₂ - k) ∈ VC := by
        have he1 : h'' 0 = h' d := by rw [hh'' 0, Nat.add_zero]
        have he2 : h'' 1 = h' (d + 1) := by rw [hh'' 1]
        rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [hgR k, he1] at e1
          rw [hgR (k + 1), he2, show j₂ - (k + 1) = j₂ - k - 1 from by omega] at e2
          exact ⟨by rw [e2]; exact hVCall (d + 1), by rw [e1]; exact hVCall d⟩
        · rw [hgR k, he2] at e1
          rw [hgR (k + 1), he1, show j₂ - (k + 1) = j₂ - k - 1 from by omega] at e2
          exact ⟨by rw [e2]; exact hVCall d, by rw [e1]; exact hVCall (d + 1)⟩
      obtain ⟨ha0, hj₂1'⟩ := hVCstep (j₂ - k - 1)
        (by omega) hind.1
        (by rw [show j₂ - k - 1 + 1 = j₂ - k from by omega]; exact hind.2)
      -- so j₂ = 1 and the only step is the chord {x₀, u₀}
      have hk0 : k = 0 := by omega
      subst hk0
      rcases hmatch with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · -- gR 0 = h'' 0 = h' d and gR 1 = h'' 1 = h' (d+1)
        have e1' : gR 0 = h'' 0 := e1
        have e2' : gR 1 = h'' 1 := e2
        rw [hgR 0, Nat.sub_zero, hj₂1', hg₂1, hh'' 0, Nat.add_zero] at e1'
        rw [hgR 1, hj₂1', Nat.sub_self, hg₂0, ← h'0, hh'' 1] at e2'
        -- e1' : u₀ = h' d ; e2' : h' 0 = h' (d + 1)
        rcases Nat.lt_or_ge (d + 1) m with h1 | h1
        · have := h'inj 0 (d + 1) (by omega) h1 e2'
          omega
        · have hdm1 : d = m - 1 := by omega
          rw [hh' d, hdm1] at e1'
          exact hu₀2 e1'
      · -- gR 0 = h' (d+1) and gR 1 = h' d
        have e1' : gR 0 = h'' 1 := e1
        have e2' : gR 1 = h'' 0 := e2
        rw [hgR 0, Nat.sub_zero, hj₂1', hg₂1, hh'' 1] at e1'
        rw [hgR 1, hj₂1', Nat.sub_self, hg₂0, ← h'0, hh'' 0, Nat.add_zero] at e2'
        -- e2' : h' 0 = h' d
        have := h'inj 0 d (by omega) hdm e2'
        omega

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (W : Finset (Fin n)) (hW : Even W.card)
    (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hfrac : ∀ u v, y u v ≠ 0 → y u v < 1)
    (hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ z : Fin n → Fin n → ℝ, z ≠ 0 ∧ (∀ u v, z u v = z v u) ∧
      (∀ v, z v v = 0) ∧ (∀ u v, z u v ≠ 0 → y u v ≠ 0) ∧
      (∀ v, ∑ u, z v u = 0) := by
  obtain ⟨z, h1, h2, h3, h4, h5⟩ :=
    support_perturbation_thm W hW hWn y hsym hdiag hsupp hdeg hfrac hodd
  exact ⟨z, h1, h2, h3, h4, h5⟩
