-- Prove2me | solution 1 for lean_workbook_plus_64142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:09:57.476695+00:00
-- url     : https://prove2.me/submissions/cd8db5bb-3a5c-453c-b537-75f29c475fcd

import Mathlib

open scoped BigOperators

namespace SignedQuadraticPrefixRepresentation

def weight (d : ℤ) (i : ℕ) : ℤ := (1 + (i + 1 : ℕ) * d) ^ 2

def Represents (d z : ℤ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ e : ℕ → ℤ,
    (∀ i, e i = 1 ∨ e i = -1) ∧
    ∑ i ∈ Finset.range n, e i * weight d i = z

theorem four_block (d : ℤ) (n : ℕ) :
    weight d n - weight d (n + 1) - weight d (n + 2) + weight d (n + 3) =
      4 * d ^ 2 := by
  simp only [weight, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem append_four {d z : ℤ} (h : Represents d z) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : Represents d (z + s * (4 * d ^ 2)) := by
  obtain ⟨n, hn, e, he, hz⟩ := h
  let e' : ℕ → ℤ := fun i =>
    if i < n then e i else if i = n ∨ i = n + 3 then s else -s
  refine ⟨n + 4, by omega, e', ?_, ?_⟩
  · intro i
    dsimp [e']
    split_ifs
    · exact he i
    · exact hs
    · rcases hs with rfl | rfl <;> norm_num
  · rw [Finset.sum_range_add]
    have hfirst : (∑ i ∈ Finset.range n, e' i * weight d i) = z := by
      rw [← hz]
      apply Finset.sum_congr rfl
      intro i hi
      simp [e', Finset.mem_range.mp hi]
    rw [hfirst]
    have h0 : e' n = s := by simp [e']
    have h1 : e' (n + 1) = -s := by simp [e']
    have h2 : e' (n + 2) = -s := by simp [e']
    have h3 : e' (n + 3) = s := by simp [e']
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.add_zero, h0, h1, h2, h3]
    linear_combination s * four_block d n

theorem add_multiple {d z : ℤ} (h : Represents d z) (q : ℤ) :
    Represents d (z + q * (4 * d ^ 2)) := by
  induction q using Int.induction_on with
  | zero => simpa using h
  | succ q ih =>
      convert append_four ih 1 (Or.inl rfl) using 1
      ring
  | pred q ih =>
      convert append_four ih (-1) (Or.inr rfl) using 1
      ring

theorem signed_sum (f : ℕ → ℤ) (s t : Finset ℕ) (ht : t ⊆ s) :
    (∑ i ∈ s, (if i ∈ t then (-1 : ℤ) else 1) * f i) =
      (∑ i ∈ s, f i) - 2 * ∑ i ∈ t, f i := by
  have hi : (∑ i ∈ s, if i ∈ t then f i else 0) = ∑ i ∈ t, f i := by
    rw [← Finset.sum_subset ht]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    · intro i _ hi
      simp [hi]
  calc
    _ = ∑ i ∈ s, (f i - 2 * (if i ∈ t then f i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hi]

theorem parity_prefix (f : ℕ → ℤ) (L : ℕ) (S : ℤ) (hodd : f L % 2 = 1) :
    ∃ N : ℕ, L ≤ N ∧ (N = L ∨ N = L + 1) ∧
      2 ∣ (∑ i ∈ Finset.range N, f i) - S := by
  by_cases h : 2 ∣ (∑ i ∈ Finset.range L, f i) - S
  · exact ⟨L, le_rfl, Or.inl rfl, h⟩
  · refine ⟨L + 1, by omega, Or.inr rfl, ?_⟩
    rw [Int.dvd_iff_emod_eq_zero] at h ⊢
    rw [Finset.sum_range_succ]
    have hr := Int.emod_nonneg ((∑ i ∈ Finset.range L, f i) - S) (by norm_num : (2 : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos ((∑ i ∈ Finset.range L, f i) - S) (by norm_num : (0 : ℤ) < 2)
    omega

theorem exists_signs_mod (f : ℕ → ℤ) (M N : ℕ) (hM : 0 < M)
    (j : ℕ → ℕ) (hj : Function.Injective j)
    (hjN : ∀ i < M, j i < N)
    (hjmod : ∀ i < M, (M : ℤ) ∣ f (j i) - 1)
    (S : ℤ) (hpar : 2 ∣ (∑ i ∈ Finset.range N, f i) - S) :
    ∃ e : ℕ → ℤ, (∀ i, e i = 1 ∨ e i = -1) ∧
      (M : ℤ) ∣ (∑ i ∈ Finset.range N, e i * f i) - S := by
  let A : ℤ := (∑ i ∈ Finset.range N, f i) - S
  let a : ℤ := A / 2
  let k : ℕ := (a % (M : ℤ)).toNat
  have hMi : (0 : ℤ) < M := by exact_mod_cast hM
  have hkcast : (k : ℤ) = a % (M : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMi))
  have hkM : k < M := by
    have := Int.emod_lt_of_pos a hMi
    exact_mod_cast (show (k : ℤ) < M by omega)
  let t : Finset ℕ := (Finset.range k).image j
  have ht : t ⊆ Finset.range N := by
    intro i hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hjN r (lt_trans (Finset.mem_range.mp hr) hkM))
  have htcard : t.card = k := by simp [t, Finset.card_image_of_injective _ hj]
  have htmod : (M : ℤ) ∣ (∑ i ∈ t, f i) - k := by
    have hsum : (M : ℤ) ∣ ∑ i ∈ t, (f i - 1) := by
      apply Finset.dvd_sum
      intro i hi
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
      exact hjmod r (lt_trans (Finset.mem_range.mp hr) hkM)
    simpa [Finset.sum_sub_distrib, htcard] using hsum
  have hrem : (M : ℤ) ∣ a - k := by
    have he : a % (M : ℤ) ≡ a [ZMOD (M : ℤ)] := by
      simp [Int.ModEq]
    simpa [hkcast] using he.dvd
  have hA : a * 2 = A := Int.ediv_mul_cancel hpar
  refine ⟨fun i => if i ∈ t then -1 else 1, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs <;> simp
  · rw [signed_sum f (Finset.range N) t ht]
    obtain ⟨u, hu⟩ := htmod
    obtain ⟨v, hv⟩ := hrem
    refine ⟨2 * (v - u), ?_⟩
    dsimp [A] at hA
    linear_combination -hA + 2 * hv - 2 * hu

theorem every_integer (d S : ℤ) (hd : 0 < d) : Represents d S := by
  let M : ℕ := 4 * d.toNat ^ 2
  let L : ℕ := M * M + 1
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hdNat : 0 < d.toNat := by exact_mod_cast (show (0 : ℤ) < d.toNat by omega)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMcast : (M : ℤ) = 4 * d ^ 2 := by simp [M, hdcast]
  have hm2 : (M : ℤ) % 2 = 0 := by rw [hMcast]; omega
  have hodd : weight d L % 2 = 1 := by
    simp [weight, L, Nat.cast_add, Nat.cast_mul, pow_two, Int.add_emod, Int.mul_emod, hm2]
  obtain ⟨N, hLN, _, hpar⟩ := parity_prefix (weight d) L S hodd
  have hN : 0 < N := by dsimp [L] at hLN; omega
  let j : ℕ → ℕ := fun i => M * (i + 1) - 1
  have hjsucc : ∀ i, j i + 1 = M * (i + 1) := by
    intro i
    have hp : 0 < M * (i + 1) := Nat.mul_pos hM (by omega)
    dsimp [j]
    omega
  have hj : Function.Injective j := by
    intro i k he
    have hm : M * (i + 1) = M * (k + 1) := by rw [← hjsucc, ← hjsucc, he]
    have := Nat.mul_left_cancel hM hm
    omega
  have hjN : ∀ i < M, j i < N := by
    intro i hi
    have hm := Nat.mul_le_mul_left M (show i + 1 ≤ M by omega)
    have hs := hjsucc i
    dsimp [L] at hLN
    omega
  have hjmod : ∀ i < M, (M : ℤ) ∣ weight d (j i) - 1 := by
    intro i _
    simp only [weight, hjsucc, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    refine ⟨2 * (i + 1) * d + (M : ℤ) * (i + 1) ^ 2 * d ^ 2, ?_⟩
    ring
  obtain ⟨e, he, hmod⟩ := exists_signs_mod (weight d) M N hM j hj hjN hjmod S hpar
  have hr : Represents d (∑ i ∈ Finset.range N, e i * weight d i) :=
    ⟨N, hN, e, he, rfl⟩
  obtain ⟨q, hq⟩ := hmod
  convert add_multiple hr (-q) using 1
  rw [← hMcast]
  linear_combination -hq

theorem source (d S : ℤ) (hd : 0 < d) :
    ∃ n : ℕ, 0 < n ∧ ∃ e : Fin n → ℤ,
      (∀ i, e i = 1 ∨ e i = -1) ∧
      ∑ i : Fin n, e i * (1 + ((i.val + 1 : ℕ) : ℤ) * d) ^ 2 = S := by
  obtain ⟨n, hn, e, he, hz⟩ := every_integer d S hd
  refine ⟨n, hn, fun i => e i.val, fun i => he i.val, ?_⟩
  change (∑ i : Fin n, e i.val * weight d i.val) = S
  rw [Fin.sum_univ_eq_sum_range (fun i => e i * weight d i) n]
  exact hz

end SignedQuadraticPrefixRepresentation

theorem solution (d S : ℤ) (hd : d > 0) :
    ∃ n : ℕ, ∃ e : Fin n → ℤ, ∑ i, e i * (1 + i * d) ^ 2 = S := by
  obtain ⟨n, _, e, _, he⟩ := SignedQuadraticPrefixRepresentation.source d S hd
  refine ⟨n + 1, Fin.cases 0 e, ?_⟩
  rw [Fin.sum_univ_succ]
  simpa using he

#print axioms SignedQuadraticPrefixRepresentation.weight
#print axioms SignedQuadraticPrefixRepresentation.Represents
#print axioms SignedQuadraticPrefixRepresentation.four_block
#print axioms SignedQuadraticPrefixRepresentation.append_four
#print axioms SignedQuadraticPrefixRepresentation.add_multiple
#print axioms SignedQuadraticPrefixRepresentation.signed_sum
#print axioms SignedQuadraticPrefixRepresentation.parity_prefix
#print axioms SignedQuadraticPrefixRepresentation.exists_signs_mod
#print axioms SignedQuadraticPrefixRepresentation.every_integer
#print axioms SignedQuadraticPrefixRepresentation.source
#print axioms solution
