-- Prove2me | solution 1 for ProofsInTheBook.Chapter27.chapter27
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:13:05.551225+00:00
-- url     : https://prove2.me/submissions/8f7560b8-4d9f-4a78-8f34-3af4236ac54a

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter27


/-!
# Chapter 27: Tiling rectangles

From "Proofs from THE BOOK":

**De Bruijn's theorem**: An a × b rectangle can be tiled by 1 × n
rectangles iff n divides a or n divides b.

*Book proof (necessity).* Let ω = e^{2πi/n} (primitive n-th root of unity).
Assign weight ω^{i+j} to cell (i, j). Any 1×n horizontal brick in row r
starting at column c has weight ω^{r+c}(1+ω+...+ω^{n-1}) = 0.  Any n×1
vertical brick in column c starting at row r has weight the same = 0.
So the total weight of the whole tiling is 0.  But the total also factors as
(∑_{i<a} ω^i)(∑_{j<b} ω^j).  Since ℂ is an integral domain, one factor is 0,
so n|a or n|b.
-/

namespace ProofsInTheBook.Chapter27

open Complex Finset Real IsPrimitiveRoot

/-! ### The coloring argument -/



private lemma omega_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (ω n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- The key vanishing: ∑_{k=0}^{n-1} ω^k = 0 for n ≥ 2. -/
private lemma geom_sum_omega_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, (ω n) ^ k = 0 :=
  (omega_isPrimitiveRoot n (by omega)).geom_sum_eq_zero (by omega)

/-- Any n consecutive powers of ω sum to 0. -/
private lemma consecutive_sum_zero (n : ℕ) (hn : 2 ≤ n) (base : ℕ) :
    ∑ k ∈ range n, (ω n) ^ (base + k) = 0 := by
  simp_rw [pow_add, ← mul_sum]
  rw [geom_sum_omega_zero n hn, mul_zero]

/-- The rectangle sum factors as a product of two geometric sums. -/
private lemma rect_sum_eq_product (n a b : ℕ) :
    ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) =
    (∑ i ∈ range a, (ω n) ^ i) * (∑ j ∈ range b, (ω n) ^ j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => (ω n) ^ i) a,
      ← Fin.sum_univ_eq_sum_range (fun j => (ω n) ^ j) b]
  simp_rw [pow_add, ← Finset.mul_sum, ← Finset.sum_mul]

/-- ∑_{k=0}^{m-1} ω^k = 0 if and only if n | m. -/
private lemma geom_sum_zero_iff_dvd (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ∑ k ∈ range m, (ω n) ^ k = 0 ↔ n ∣ m := by
  have hωprim := omega_isPrimitiveRoot n (by omega)
  constructor
  · intro h
    by_contra hndvd
    have hω1 : ω n ≠ 1 := hωprim.ne_one (by omega)
    rw [geom_sum_eq hω1] at h
    exact absurd h (div_ne_zero
      (sub_ne_zero.mpr (fun heq => hndvd (hωprim.dvd_of_pow_eq_one m heq)))
      (sub_ne_zero.mpr hω1))
  · intro ⟨q, hq⟩
    subst hq
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simp_rw [show ∀ k : ℕ, (ω n) ^ (n * q + k) = (ω n) ^ k from
        fun k => by rw [pow_add, pow_mul, hωprim.pow_eq_one, one_pow, one_mul]]
      exact hωprim.geom_sum_eq_zero (by omega)

/-! ### The tiling model -/



private def hBrick (n a b : ℕ) (r : Fin a) (c : ℕ) : Finset (Fin a × Fin b) :=
  Finset.univ.filter (fun p : Fin a × Fin b =>
    p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n)

private def vBrick (n a b : ℕ) (col : Fin b) (r : ℕ) : Finset (Fin a × Fin b) :=
  Finset.univ.filter (fun p : Fin a × Fin b =>
    p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n)

/-- The horizontal brick sum is zero. -/
private lemma hBrick_sum_zero (n a b : ℕ) (hn : 2 ≤ n) (r : Fin a) (c : ℕ) (hc : c + n ≤ b) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin b =>
        p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n),
      (ω n) ^ (p.1.val + p.2.val) = 0 := by
  -- Reindex: the brick is in bijection with {0, ..., n-1} via k ↦ (r, c+k)
  have heq : (Finset.univ.filter (fun p : Fin a × Fin b =>
      p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n)) =
      Finset.univ.image
        (fun k : Fin n => (r, (⟨c + k.val, by
          have hk := k.isLt
          omega⟩ : Fin b))) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨rfl, hcy, hyc⟩
      refine ⟨⟨y.val - c, by omega⟩, ?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp
        omega
    · rintro ⟨k, hxy⟩
      have hx : x = r := (Prod.ext_iff.mp hxy).1.symm
      have hyval : y.val = c + k.val := by
        have hy : (⟨c + k.val, by
          have hk := k.isLt
          omega⟩ : Fin b) = y := (Prod.ext_iff.mp hxy).2
        simpa using congrArg (fun z : Fin b => z.val) hy.symm
      refine ⟨hx, ?_, ?_⟩
      · omega
      · have hk := k.isLt
        omega
  rw [heq, sum_image]
  · have hfin : (∑ k : Fin n, (ω n) ^ (r.val + (c + k.val))) =
        ∑ k ∈ range n, (ω n) ^ (r.val + c + k) := by
      calc
        (∑ k : Fin n, (ω n) ^ (r.val + (c + k.val)))
            = ∑ k : Fin n, (ω n) ^ (r.val + c + k.val) := by
          apply sum_congr rfl
          intro k _hk
          congr 1
          omega
        _ = ∑ k ∈ range n, (ω n) ^ (r.val + c + k) := by
          exact Fin.sum_univ_eq_sum_range (fun k => (ω n) ^ (r.val + c + k)) n
    rw [hfin]
    exact consecutive_sum_zero n hn (r.val + c)
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    have hv := congrArg (fun p : Fin a × Fin b => p.2.val) h
    simp at hv
    omega

/-- The vertical brick sum is zero. -/
private lemma vBrick_sum_zero (n a b : ℕ) (hn : 2 ≤ n) (col : Fin b) (r : ℕ) (hr : r + n ≤ a) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin b =>
        p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n),
      (ω n) ^ (p.1.val + p.2.val) = 0 := by
  have heq : (Finset.univ.filter (fun p : Fin a × Fin b =>
      p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n)) =
      Finset.univ.image
        (fun k : Fin n => ((⟨r + k.val, by
          have hk := k.isLt
          omega⟩ : Fin a), col)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨rfl, hrx, hxr⟩
      refine ⟨⟨x.val - r, by omega⟩, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        simp
        omega
      · rfl
    · rintro ⟨k, hxy⟩
      have hy : y = col := (Prod.ext_iff.mp hxy).2.symm
      have hxval : x.val = r + k.val := by
        have hx : (⟨r + k.val, by
          have hk := k.isLt
          omega⟩ : Fin a) = x := (Prod.ext_iff.mp hxy).1
        simpa using congrArg (fun z : Fin a => z.val) hx.symm
      refine ⟨hy, ?_, ?_⟩
      · omega
      · have hk := k.isLt
        omega
  rw [heq, sum_image]
  · have hfin : (∑ k : Fin n, (ω n) ^ ((r + k.val) + col.val)) =
        ∑ k ∈ range n, (ω n) ^ (r + col.val + k) := by
      calc
        (∑ k : Fin n, (ω n) ^ ((r + k.val) + col.val))
            = ∑ k : Fin n, (ω n) ^ (r + col.val + k.val) := by
          apply sum_congr rfl
          intro k _hk
          congr 1
          omega
        _ = ∑ k ∈ range n, (ω n) ^ (r + col.val + k) := by
          exact Fin.sum_univ_eq_sum_range (fun k => (ω n) ^ (r + col.val + k)) n
    rw [hfin]
    exact consecutive_sum_zero n hn (r + col.val)
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    have hv := congrArg (fun p : Fin a × Fin b => p.1.val) h
    simp at hv
    omega

/-- If the rectangle is tiled by 1×n bricks, the coloring sum is zero. -/
private lemma tiling_implies_sum_zero (n a b : ℕ) (hn : 2 ≤ n)
    (htile : IsTiledByNxOne n a b) :
    ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) = 0 := by
  obtain ⟨bricks, hcover, hdisj, hbrick⟩ := htile
  have hpwd : (↑bricks : Set _).PairwiseDisjoint id := fun B₁ hB₁ B₂ hB₂ hne =>
    hdisj B₁ (Finset.mem_coe.mp hB₁) B₂ (Finset.mem_coe.mp hB₂) hne
  -- Convert iterated sum to sum over all cells
  rw [show ∑ i : Fin a, ∑ j : Fin b, (ω n) ^ (i.val + j.val) =
      ∑ p : Fin a × Fin b, (ω n) ^ (p.1.val + p.2.val) from by simp [← sum_product']]
  -- Convert sum over cells to sum over bricks via partition
  rw [← hcover, Finset.sum_biUnion hpwd]
  simp only [id]
  apply sum_eq_zero
  intro B hB
  rcases hbrick B hB with ⟨r, c, hc, rfl⟩ | ⟨col, r, hr, rfl⟩
  · exact hBrick_sum_zero n a b hn r c hc
  · exact vBrick_sum_zero n a b hn col r hr

/-! ### Explicit tilings for the converse -/

private lemma tiled_of_dvd_width (n a b : ℕ) (hnpos : 0 < n) (hb : n ∣ b) :
    IsTiledByNxOne n a b := by
  obtain ⟨q, rfl⟩ := hb
  let brick : Fin a × Fin q → Finset (Fin a × Fin (n * q)) := fun idx =>
    hBrick n a (n * q) idx.1 (idx.2.val * n)
  refine ⟨Finset.univ.image brick, ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro _hp
      exact Finset.mem_univ p
    · intro _hp
      let t : Fin q := ⟨p.2.val / n, Nat.div_lt_of_lt_mul p.2.isLt⟩
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨brick (p.1, t), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(p.1, t), Finset.mem_univ _, rfl⟩
      · change p ∈ brick (p.1, t)
        simp only [brick, hBrick, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Nat.div_mul_le_self p.2.val n, ?_⟩
        calc
          p.2.val = (p.2.val / n) * n + p.2.val % n := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod p.2.val n).symm
          _ < (p.2.val / n) * n + n :=
            Nat.add_lt_add_left (Nat.mod_lt _ hnpos) _
  · intro B₁ hB₁ B₂ hB₂ hne
    rcases Finset.mem_image.mp hB₁ with ⟨i₁, _hi₁, rfl⟩
    rcases Finset.mem_image.mp hB₂ with ⟨i₂, _hi₂, rfl⟩
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    have hp₁' :
        p.1 = i₁.1 ∧ i₁.2.val * n ≤ p.2.val ∧ p.2.val < i₁.2.val * n + n := by
      simpa [brick, hBrick] using hp₁
    have hp₂' :
        p.1 = i₂.1 ∧ i₂.2.val * n ≤ p.2.val ∧ p.2.val < i₂.2.val * n + n := by
      simpa [brick, hBrick] using hp₂
    have hrow : i₁.1 = i₂.1 := hp₁'.1.symm.trans hp₂'.1
    have hlt₁ : p.2.val < (i₁.2.val + 1) * n := by
      simpa [Nat.add_mul, Nat.one_mul] using hp₁'.2.2
    have hlt₂ : p.2.val < (i₂.2.val + 1) * n := by
      simpa [Nat.add_mul, Nat.one_mul] using hp₂'.2.2
    have hdiv₁ : p.2.val / n = i₁.2.val :=
      Nat.div_eq_of_lt_le hp₁'.2.1 hlt₁
    have hdiv₂ : p.2.val / n = i₂.2.val :=
      Nat.div_eq_of_lt_le hp₂'.2.1 hlt₂
    have hblock : i₁.2 = i₂.2 := by
      apply Fin.ext
      exact hdiv₁.symm.trans hdiv₂
    have hidx : i₁ = i₂ := Prod.ext hrow hblock
    exact hne (by rw [hidx])
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨idx, _hidx, rfl⟩
    left
    refine ⟨idx.1, idx.2.val * n, ?_, ?_⟩
    · calc
        idx.2.val * n + n = (idx.2.val + 1) * n := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ q * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt idx.2.isLt)
        _ = n * q := Nat.mul_comm q n
    · rfl

private lemma tiled_of_dvd_height (n a b : ℕ) (hnpos : 0 < n) (ha : n ∣ a) :
    IsTiledByNxOne n a b := by
  obtain ⟨q, rfl⟩ := ha
  let brick : Fin q × Fin b → Finset (Fin (n * q) × Fin b) := fun idx =>
    vBrick n (n * q) b idx.2 (idx.1.val * n)
  refine ⟨Finset.univ.image brick, ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro _hp
      exact Finset.mem_univ p
    · intro _hp
      let t : Fin q := ⟨p.1.val / n, Nat.div_lt_of_lt_mul p.1.isLt⟩
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨brick (t, p.2), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(t, p.2), Finset.mem_univ _, rfl⟩
      · change p ∈ brick (t, p.2)
        simp only [brick, vBrick, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Nat.div_mul_le_self p.1.val n, ?_⟩
        calc
          p.1.val = (p.1.val / n) * n + p.1.val % n := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod p.1.val n).symm
          _ < (p.1.val / n) * n + n :=
            Nat.add_lt_add_left (Nat.mod_lt _ hnpos) _
  · intro B₁ hB₁ B₂ hB₂ hne
    rcases Finset.mem_image.mp hB₁ with ⟨i₁, _hi₁, rfl⟩
    rcases Finset.mem_image.mp hB₂ with ⟨i₂, _hi₂, rfl⟩
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    have hp₁' :
        p.2 = i₁.2 ∧ i₁.1.val * n ≤ p.1.val ∧ p.1.val < i₁.1.val * n + n := by
      simpa [brick, vBrick] using hp₁
    have hp₂' :
        p.2 = i₂.2 ∧ i₂.1.val * n ≤ p.1.val ∧ p.1.val < i₂.1.val * n + n := by
      simpa [brick, vBrick] using hp₂
    have hcol : i₁.2 = i₂.2 := hp₁'.1.symm.trans hp₂'.1
    have hlt₁ : p.1.val < (i₁.1.val + 1) * n := by
      simpa [Nat.add_mul, Nat.one_mul] using hp₁'.2.2
    have hlt₂ : p.1.val < (i₂.1.val + 1) * n := by
      simpa [Nat.add_mul, Nat.one_mul] using hp₂'.2.2
    have hdiv₁ : p.1.val / n = i₁.1.val :=
      Nat.div_eq_of_lt_le hp₁'.2.1 hlt₁
    have hdiv₂ : p.1.val / n = i₂.1.val :=
      Nat.div_eq_of_lt_le hp₂'.2.1 hlt₂
    have hblock : i₁.1 = i₂.1 := by
      apply Fin.ext
      exact hdiv₁.symm.trans hdiv₂
    have hidx : i₁ = i₂ := Prod.ext hblock hcol
    exact hne (by rw [hidx])
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨idx, _hidx, rfl⟩
    right
    refine ⟨idx.2, idx.1.val * n, ?_, ?_⟩
    · calc
        idx.1.val * n + n = (idx.1.val + 1) * n := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ q * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt idx.1.isLt)
        _ = n * q := Nat.mul_comm q n
    · rfl

/-! ### Main theorem -/

/--
**De Bruijn's theorem**: An a × b rectangle can be tiled by 1 × n bricks
if and only if n | a or n | b.

The forward direction is de Bruijn's root-of-unity coloring argument.  The
reverse direction is the explicit grid tiling: if n divides the height, stack
n×1 bricks in each column; if n divides the width, lay 1×n bricks in each row.
-/
theorem chapter27_necessity (n a b : ℕ) (hn : 2 ≤ n) (htile : IsTiledByNxOne n a b) :
    n ∣ a ∨ n ∣ b := by
  have hsum := tiling_implies_sum_zero n a b hn htile
  rw [rect_sum_eq_product n a b] at hsum
  rcases mul_eq_zero.mp hsum with ha | hb
  · left;  exact (geom_sum_zero_iff_dvd n hn a).mp ha
  · right; exact (geom_sum_zero_iff_dvd n hn b).mp hb

theorem chapter27_converse (n a b : ℕ) (hn : 2 ≤ n) :
    n ∣ a ∨ n ∣ b → IsTiledByNxOne n a b := by
  intro hdiv
  have hnpos : 0 < n := by omega
  rcases hdiv with ha | hb
  · exact tiled_of_dvd_height n a b hnpos ha
  · exact tiled_of_dvd_width n a b hnpos hb

theorem chapter27_debruijn (n a b : ℕ) (hn : 2 ≤ n) :
    IsTiledByNxOne n a b ↔ n ∣ a ∨ n ∣ b :=
  ⟨chapter27_necessity n a b hn, chapter27_converse n a b hn⟩



end ProofsInTheBook.Chapter27

open Complex Finset Real IsPrimitiveRoot
open ProofsInTheBook.Chapter27

theorem solution (n a b : ℕ) (hn : 2 ≤ n) :
    IsTiledByNxOne n a b ↔ n ∣ a ∨ n ∣ b :=
  chapter27_debruijn n a b hn
