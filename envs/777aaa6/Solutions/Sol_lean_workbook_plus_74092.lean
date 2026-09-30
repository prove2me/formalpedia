-- Prove2me | solution 1 for lean_workbook_plus_74092
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:06:19.482895+00:00
-- url     : https://prove2.me/submissions/3c3b8b5e-a606-4737-8980-dd091198fc68

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 20000

namespace BinaryTernaryFunctionalPairCount

-- The encoding and its recursion are attributed to owned workbook54714,
-- submission091c388a-3763-4b5f-b946-cecf85dbfe22, not a new construction.
def encoding : ℕ → ℕ :=
  Nat.evenOddRec 0 (fun _ v => 3 * v) (fun _ v => 3 * v + 1)

theorem encoding_zero : encoding 0 = 0 := rfl

theorem encoding_even (n : ℕ) : encoding (2 * n) = 3 * encoding n :=
  Nat.evenOddRec_even _ _ _ rfl n

theorem encoding_odd (n : ℕ) : encoding (2 * n + 1) = 3 * encoding n + 1 :=
  Nat.evenOddRec_odd _ _ _ rfl n

theorem encoding_one : encoding 1 = 1 := by
  simpa [encoding_zero] using encoding_odd 0

def Equation (f : ℕ → ℕ) : Prop :=
  f 1 = 1 ∧ ∀ n : ℕ, 0 < n →
    3 * f n * f (2 * n + 1) = f (2 * n) * (1 + 3 * f n) ∧
      f (2 * n) < 6 * f n

theorem source_positive {f : ℕ → ℕ} (hf : Equation f) (n : ℕ) (hn : 0 < n) :
    0 < f n := by
  have h := (hf.2 n hn).2
  by_contra hz
  have he : f n = 0 := by omega
  simp [he] at h

theorem nonlinear_reduction {f : ℕ → ℕ} (hf : Equation f) (n : ℕ) (hn : 0 < n) :
    f (2 * n) = 3 * f n ∧ f (2 * n + 1) = 3 * f n + 1 := by
  have hp := source_positive hf n hn
  have hp2 := source_positive hf (2 * n) (by omega)
  have he := (hf.2 n hn).1
  have hb := (hf.2 n hn).2
  have hc : Nat.Coprime (3 * f n) (1 + 3 * f n) := by simp
  have hd : 3 * f n ∣ f (2 * n) * (1 + 3 * f n) := ⟨f (2 * n + 1), he.symm⟩
  obtain ⟨q, hq⟩ := hc.dvd_of_dvd_mul_right hd
  have hq1 : q = 1 := by
    have hq0 : 0 < q := by nlinarith
    have hq2 : q < 2 := by nlinarith
    omega
  have heven : f (2 * n) = 3 * f n := by simpa [hq1] using hq
  refine ⟨heven, ?_⟩
  rw [heven] at he
  have hh := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * f n) he
  omega

-- Positive-index uniqueness adapts the attributed encoding classification;
-- unlike its all-index version, the present source leaves f(0) arbitrary.
theorem positive_linear_unique (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hr : ∀ n : ℕ, 0 < n → f (2 * n) = 3 * f n ∧
      f (2 * n + 1) = 3 * f n + 1) (n : ℕ) :
    0 < n → f n = encoding n := by
  refine Nat.evenOddRec ?_ ?_ ?_ n
  · omega
  · intro k ih hk
    have hk0 : 0 < k := by omega
    rw [(hr k hk0).1, encoding_even, ih hk0]
  · intro k ih _
    by_cases hk : k = 0
    · simpa [hk, encoding_one] using h1
    · have hk0 : 0 < k := by omega
      rw [(hr k hk0).2, encoding_odd, ih hk0]

theorem encoding_lt_succ (n : ℕ) : encoding n < encoding (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with hzero | hone
    · have hn : n = 2 * (n / 2) := by omega
      rw [hn, encoding_even, encoding_odd]
      omega
    · have hn : n = 2 * (n / 2) + 1 := by omega
      have hk : n / 2 < n := by omega
      have hh := ih (n / 2) hk
      rw [hn, show 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) by omega,
        encoding_odd, encoding_even]
      omega

theorem encoding_strictMono : StrictMono encoding :=
  strictMono_nat_of_lt_succ encoding_lt_succ

theorem encoding_lower (n : ℕ) : n ≤ encoding n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hh := encoding_lt_succ n
    omega

theorem source_classification (f : ℕ → ℕ) :
    Equation f ↔ ∀ n : ℕ, 0 < n → f n = encoding n := by
  constructor
  · intro hf
    exact positive_linear_unique f hf.1 (nonlinear_reduction hf)
  · intro hf
    refine ⟨by simpa [encoding_one] using hf 1 (by omega), ?_⟩
    intro n hn
    rw [hf n hn, hf (2 * n) (by omega), hf (2 * n + 1) (by omega),
      encoding_even, encoding_odd]
    have hp : 0 < encoding n := lt_of_lt_of_le hn (encoding_lower n)
    constructor
    · ring
    · omega

def extension (c n : ℕ) : ℕ := if n = 0 then c else encoding n

theorem extension_model (c : ℕ) : Equation (extension c) := by
  apply (source_classification _).2
  intro n hn
  simp [extension, Nat.ne_of_gt hn]

theorem full_extension_classification (f : ℕ → ℕ) :
    Equation f ↔ f = extension (f 0) := by
  rw [source_classification]
  constructor
  · intro hf
    funext n
    by_cases hn : n = 0
    · simp [extension, hn]
    · simpa [extension, hn] using hf n (by omega)
  · intro hf n hn
    rw [hf]
    simp [extension, Nat.ne_of_gt hn]

def pairs : Finset (ℕ × ℕ) :=
  {(5, 47), (7, 45), (13, 39), (15, 37),
    (37, 15), (39, 13), (45, 7), (47, 5)}

theorem encoding_sixty_four : encoding 64 = 729 := by
  decide +kernel

theorem sum_bound (k m : ℕ) (h : encoding k + encoding m = 293) :
    k < 64 ∧ m < 64 := by
  constructor
  · by_contra hk
    have hh := encoding_strictMono.monotone (show 64 ≤ k by omega)
    rw [encoding_sixty_four] at hh
    omega
  · by_contra hm
    have hh := encoding_strictMono.monotone (show 64 ≤ m by omega)
    rw [encoding_sixty_four] at hh
    omega

theorem bounded_pair_classification :
    ∀ k m : Fin 64, encoding k.val + encoding m.val = 293 ↔ (k.val, m.val) ∈ pairs := by
  decide +kernel

theorem encoding_pair_classification (k m : ℕ) :
    encoding k + encoding m = 293 ↔ (k, m) ∈ pairs := by
  constructor
  · intro h
    have hb := sum_bound k m h
    exact (bounded_pair_classification ⟨k, hb.1⟩ ⟨m, hb.2⟩).1 h
  · intro h
    have hb : k < 64 ∧ m < 64 := by
      simp only [pairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
      rcases h with h | h | h | h | h | h | h | h <;> omega
    exact (bounded_pair_classification ⟨k, hb.1⟩ ⟨m, hb.2⟩).2 h

theorem pairs_positive (p : ℕ × ℕ) (hp : p ∈ pairs) : 0 < p.1 ∧ 0 < p.2 := by
  simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem source_pair_classification {f : ℕ → ℕ} (hf : Equation f) (k m : ℕ) :
    (0 < k ∧ 0 < m ∧ f k + f m = 293) ↔ (k, m) ∈ pairs := by
  have he := (source_classification f).1 hf
  constructor
  · rintro ⟨hk, hm, hsum⟩
    apply (encoding_pair_classification k m).1
    simpa [he k hk, he m hm] using hsum
  · intro hp
    obtain ⟨hk, hm⟩ := pairs_positive (k, m) hp
    refine ⟨hk, hm, ?_⟩
    rw [he k hk, he m hm]
    exact (encoding_pair_classification k m).2 hp

theorem pairs_card : pairs.card = 8 := by decide

theorem source_set {f : ℕ → ℕ} (hf : Equation f) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ f p.1 + f p.2 = 293} =
      (pairs : Set (ℕ × ℕ)) := by
  ext p
  exact source_pair_classification hf p.1 p.2

theorem source_count {f : ℕ → ℕ} (hf : Equation f) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ f p.1 + f p.2 = 293}.ncard = 8 := by
  rw [source_set hf, Set.ncard_coe_finset, pairs_card]

theorem source_witness {f : ℕ → ℕ} (hf : Equation f) : f 5 + f 47 = 293 := by
  have hp : (5, 47) ∈ pairs := by decide
  exact ((source_pair_classification hf 5 47).2 hp).2.2

theorem zero_index_inconsistent (f : ℕ → ℕ)
    (hf : f 1 = 1 ∧ ∀ n, 3 * f n * f (2 * n + 1) =
      f (2 * n) * (1 + 3 * f n) ∧ f (2 * n) < 6 * f n) : False := by
  have he := (hf.2 0).1
  have hb := (hf.2 0).2
  simp only [Nat.mul_zero, Nat.zero_add, hf.1, Nat.mul_one] at he hb
  have hp : 0 < f 0 := by nlinarith
  nlinarith

end BinaryTernaryFunctionalPairCount

theorem solution (k m : ℕ) (f : ℕ → ℕ)
    (hf : f 1 = 1 ∧ ∀ n, 3 * f n * f (2 * n + 1) =
      f (2 * n) * (1 + 3 * f n) ∧ f (2 * n) < 6 * f n) :
    f k + f m = 293 :=
  False.elim (BinaryTernaryFunctionalPairCount.zero_index_inconsistent f hf)

#print axioms BinaryTernaryFunctionalPairCount.encoding
#print axioms BinaryTernaryFunctionalPairCount.encoding_zero
#print axioms BinaryTernaryFunctionalPairCount.encoding_even
#print axioms BinaryTernaryFunctionalPairCount.encoding_odd
#print axioms BinaryTernaryFunctionalPairCount.encoding_one
#print axioms BinaryTernaryFunctionalPairCount.Equation
#print axioms BinaryTernaryFunctionalPairCount.source_positive
#print axioms BinaryTernaryFunctionalPairCount.nonlinear_reduction
#print axioms BinaryTernaryFunctionalPairCount.positive_linear_unique
#print axioms BinaryTernaryFunctionalPairCount.encoding_lt_succ
#print axioms BinaryTernaryFunctionalPairCount.encoding_strictMono
#print axioms BinaryTernaryFunctionalPairCount.encoding_lower
#print axioms BinaryTernaryFunctionalPairCount.source_classification
#print axioms BinaryTernaryFunctionalPairCount.extension
#print axioms BinaryTernaryFunctionalPairCount.extension_model
#print axioms BinaryTernaryFunctionalPairCount.full_extension_classification
#print axioms BinaryTernaryFunctionalPairCount.pairs
#print axioms BinaryTernaryFunctionalPairCount.encoding_sixty_four
#print axioms BinaryTernaryFunctionalPairCount.sum_bound
#print axioms BinaryTernaryFunctionalPairCount.bounded_pair_classification
#print axioms BinaryTernaryFunctionalPairCount.encoding_pair_classification
#print axioms BinaryTernaryFunctionalPairCount.pairs_positive
#print axioms BinaryTernaryFunctionalPairCount.source_pair_classification
#print axioms BinaryTernaryFunctionalPairCount.pairs_card
#print axioms BinaryTernaryFunctionalPairCount.source_set
#print axioms BinaryTernaryFunctionalPairCount.source_count
#print axioms BinaryTernaryFunctionalPairCount.source_witness
#print axioms BinaryTernaryFunctionalPairCount.zero_index_inconsistent
#print axioms solution
