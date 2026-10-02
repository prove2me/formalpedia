-- Prove2me | solution 1 for BookSixth.latin_bounds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:30:07.431041+00:00
-- url     : https://prove2.me/submissions/11332733-9578-4cf9-97ba-677000d70b13

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BookSixth
import Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_chapter22_unconditional
import Theorems.Thm_BookSixth_bregman_minc

/-!
Latin-square counting bounds via the existing Van der Waerden and Bregman--Minc
permanent inequalities. This formalizes known textbook mathematics, not a new
mathematical result.

Target: BookSixth.latin_bounds, c6076667-303d-403a-a2bc-f424ec04ff08.
Source: Aigner--Ziegler, Proofs from THE BOOK, sixth edition (2018), Chapter 37,
Theorem 2, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37
The lower permanent bound is the existing Chapter 24 theorem; the upper bound
is Chapter 37, Theorem 1. All public definitions are imported unchanged.

The four local namespace blocks below are byte-identical to the corresponding
blocks in the verified conditional development. The final declaration supplies
the two permanent inequalities from the actual public theorem imports.
-/

set_option autoImplicit false
open scoped BigOperators

namespace BookSixth.LatinBridge

def Rectangle {r n : ℕ} (L : Fin r → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧
    ∀ c, Function.Injective (fun i => L i c)

noncomputable def rectangles (r n : ℕ) : Finset (Fin r → Fin n → Fin n) := by
  classical
  exact Finset.univ.filter Rectangle

def Allowed {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (f : Fin n → Fin n) : Prop := ∀ c i, L i c ≠ f c

noncomputable def availability {r n : ℕ} (L : Fin r → Fin n → Fin n) :
    Matrix (Fin n) (Fin n) ℕ := by
  classical
  exact fun c s => if ∀ i, L i c ≠ s then 1 else 0

noncomputable def admissibleRows {r n : ℕ} (L : Fin r → Fin n → Fin n) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun σ => Allowed L σ)

noncomputable def rowExtensions {r n : ℕ} (L : Fin r → Fin n → Fin n) :
    Finset (Fin (r + 1) → Fin n → Fin n) := by
  classical
  exact Finset.univ.filter (fun M => Rectangle M ∧ ∀ i, M i.castSucc = L i)

theorem rectangle_iff_latin {n : ℕ} (L : Fin n → Fin n → Fin n) :
    Rectangle L ↔ BookSixth.Latin L := by
  constructor
  · intro h
    exact ⟨h.1, fun c => (h.2 c).bijective_of_finite⟩
  · intro h
    exact ⟨h.1, fun c => (h.2 c).1⟩

theorem rectangles_full_card (n : ℕ) :
    (rectangles n n).card = BookSixth.latinCount n := by
  classical
  unfold rectangles BookSixth.latinCount
  congr 1
  ext L
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, rectangle_iff_latin]

theorem admissibleRows_card_eq_permanent {r n : ℕ}
    (L : Fin r → Fin n → Fin n) :
    (admissibleRows L).card = BookSixth.permanent (availability L) := by
  classical
  unfold BookSixth.permanent availability
  simp only [Fintype.prod_boole]
  calc
    (admissibleRows L).card =
        ∑ σ : Equiv.Perm (Fin n), if Allowed L σ then 1 else 0 := by
      simpa only [admissibleRows] using
        Finset.natCast_card_filter (R := ℕ)
          (fun σ : Equiv.Perm (Fin n) => Allowed L σ) Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : Allowed L σ
      · have h' : ∀ c i, L i c ≠ σ c := h
        simp only [if_pos h, if_pos h']
      · have h' : ¬ ∀ c i, L i c ≠ σ c := h
        simp only [if_neg h, if_neg h']

theorem availability_le_one {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (c s : Fin n) : availability L c s ≤ 1 := by
  classical
  simp only [availability]
  split_ifs <;> omega

private theorem missing_count {r n : ℕ} (f : Fin r → Fin n)
    (hf : Function.Injective f) :
    (∑ s : Fin n, if ∀ i, f i ≠ s then 1 else 0 : ℕ) = n - r := by
  classical
  rw [Finset.sum_boole]
  have hset : Finset.univ.filter (fun s => ∀ i, f i ≠ s) =
      Finset.univ \ Finset.univ.image f := by
    ext s
    simp
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_image_of_injective _ hf]
  simp

theorem availability_row_sum {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (hL : Rectangle L) (c : Fin n) :
    ∑ s, availability L c s = n - r := by
  classical
  exact missing_count (fun i => L i c) (hL.2 c)

theorem availability_column_sum {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (hL : Rectangle L) (s : Fin n) :
    ∑ c, availability L c s = n - r := by
  classical
  let pos : Fin r → Fin n := fun i => Classical.choose ((hL.1 i).2 s)
  have hpos (i : Fin r) : L i (pos i) = s := Classical.choose_spec ((hL.1 i).2 s)
  have hinj : Function.Injective pos := by
    intro i j hij
    apply hL.2 (pos i)
    exact (hpos i).trans ((congrArg (L j) hij).trans (hpos j)).symm
  have hallowed (c : Fin n) : (∀ i, L i c ≠ s) ↔ ∀ i, pos i ≠ c := by
    constructor
    · intro h i hi
      apply h i
      simpa only [hi] using hpos i
    · intro h i hi
      apply h i
      exact (hL.1 i).1 ((hpos i).trans hi.symm)
  calc
    (∑ c, availability L c s) =
        ∑ c : Fin n, if ∀ i, pos i ≠ c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [availability, hallowed]
    _ = n - r := missing_count pos hinj

private theorem snoc_column {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (f : Fin n → Fin n) (c : Fin n) :
    (fun i => (Fin.snoc (α := fun _ : Fin (r + 1) => Fin n → Fin n) L f i) c) =
      Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) (fun i => L i c) (f c) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem rectangle_snoc_iff {r n : ℕ} (L : Fin r → Fin n → Fin n)
    (f : Fin n → Fin n) :
    Rectangle (Fin.snoc L f) ↔
      Rectangle L ∧ Function.Bijective f ∧ Allowed L f := by
  constructor
  · intro h
    have hcol (c : Fin n) :
        Function.Injective (fun i => L i c) ∧ f c ∉ Set.range (fun i => L i c) := by
      apply Fin.snoc_injective_iff.mp
      rw [← snoc_column L f c]
      exact h.2 c
    refine ⟨⟨?_, fun c => (hcol c).1⟩, ?_, ?_⟩
    · intro i
      simpa only [Fin.snoc_castSucc] using h.1 i.castSucc
    · simpa only [Fin.snoc_last] using h.1 (Fin.last r)
    · intro c i hi
      exact (hcol c).2 ⟨i, hi⟩
  · rintro ⟨hL, hf, hallowed⟩
    constructor
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hf
      · simpa only [Fin.snoc_castSucc] using hL.1 j
    · intro c
      rw [snoc_column L f c]
      apply Fin.snoc_injective_of_injective (hL.2 c)
      rintro ⟨i, hi⟩
      exact hallowed c i hi

theorem rowExtensions_card_eq_permanent {r n : ℕ}
    (L : Fin r → Fin n → Fin n) (hL : Rectangle L) :
    (rowExtensions L).card = BookSixth.permanent (availability L) := by
  classical
  rw [← admissibleRows_card_eq_permanent L]
  symm
  apply Finset.card_bij (s := admissibleRows L) (t := rowExtensions L)
    (fun (σ : Equiv.Perm (Fin n)) _ =>
      Fin.snoc (α := fun _ : Fin (r + 1) => Fin n → Fin n) L (σ : Fin n → Fin n))
  · intro σ hσ
    have ha : Allowed L σ := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (rectangle_snoc_iff L σ).2 ⟨hL, σ.bijective, ha⟩, ?_⟩
    intro i
    exact Fin.snoc_castSucc _ _ _
  · intro σ hσ τ hτ heq
    apply Equiv.ext
    intro c
    have hlast := congrFun heq (Fin.last r)
    have hrow : (σ : Fin n → Fin n) = τ := by
      simpa only [Fin.snoc_last] using hlast
    exact congrFun hrow c
  · intro M hM
    rcases (Finset.mem_filter.mp hM).2 with ⟨hrect, hprefix⟩
    let f := M (Fin.last r)
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (hrect.1 (Fin.last r))
    have heq : Fin.snoc L f = M := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, f]
      · simpa only [Fin.snoc_castSucc] using (hprefix j).symm
    have hallowed : Allowed L f := by
      apply ((rectangle_snoc_iff L f).mp ?_).2.2
      rw [heq]
      exact hrect
    refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hallowed⟩, ?_⟩
    exact heq

end BookSixth.LatinBridge

namespace BookSixth.LatinBridge

theorem rectangles_zero_card (n : ℕ) : (rectangles 0 n).card = 1 := by
  classical
  have hall (L : Fin 0 → Fin n → Fin n) : Rectangle L := by
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro c i j _
    exact Fin.elim0 i
  simp [rectangles, hall]

theorem rectangle_prefix {r n : ℕ} (M : Fin (r + 1) → Fin n → Fin n)
    (hM : Rectangle M) : Rectangle (fun i : Fin r => M i.castSucc) := by
  refine ⟨fun i => hM.1 i.castSucc, ?_⟩
  intro c i j hij
  exact Fin.castSucc_injective _ (hM.2 c hij)

theorem rectangles_succ_card (r n : ℕ) :
    (rectangles (r + 1) n).card =
      ∑ L ∈ rectangles r n, (rowExtensions L).card := by
  classical
  let rowPrefix : (Fin (r + 1) → Fin n → Fin n) → (Fin r → Fin n → Fin n) :=
    fun M i => M i.castSucc
  have hmap : (rectangles (r + 1) n : Set (Fin (r + 1) → Fin n → Fin n)).MapsTo
      rowPrefix (rectangles r n) := by
    intro M hM
    have hm : Rectangle M := (Finset.mem_filter.mp hM).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rectangle_prefix M hm⟩
  calc
    (rectangles (r + 1) n).card =
        ∑ L ∈ rectangles r n,
          ((rectangles (r + 1) n).filter (fun M => rowPrefix M = L)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ L ∈ rectangles r n, (rowExtensions L).card := by
      apply Finset.sum_congr rfl
      intro L _
      congr 1
      ext M
      simp [rectangles, rowExtensions, rowPrefix, funext_iff]

theorem rectangle_step_bounds_of_uniform {r n : ℕ} (lo hi : ℝ)
    (hlo : ∀ L : Fin r → Fin n → Fin n, Rectangle L →
      lo ≤ ((rowExtensions L).card : ℝ))
    (hhi : ∀ L : Fin r → Fin n → Fin n, Rectangle L →
      ((rowExtensions L).card : ℝ) ≤ hi) :
    ((rectangles r n).card : ℝ) * lo ≤ ((rectangles (r + 1) n).card : ℝ) ∧
    ((rectangles (r + 1) n).card : ℝ) ≤ ((rectangles r n).card : ℝ) * hi := by
  classical
  have hcount : ((rectangles (r + 1) n).card : ℝ) =
      ∑ L ∈ rectangles r n, ((rowExtensions L).card : ℝ) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun x : ℕ => (x : ℝ)) (rectangles_succ_card r n)
  constructor
  · calc
      ((rectangles r n).card : ℝ) * lo = ∑ _L ∈ rectangles r n, lo := by
        simp
      _ ≤ ∑ L ∈ rectangles r n, ((rowExtensions L).card : ℝ) := by
        apply Finset.sum_le_sum
        intro L hL
        exact hlo L (Finset.mem_filter.mp hL).2
      _ = ((rectangles (r + 1) n).card : ℝ) := hcount.symm
  · calc
      ((rectangles (r + 1) n).card : ℝ) =
          ∑ L ∈ rectangles r n, ((rowExtensions L).card : ℝ) := hcount
      _ ≤ ∑ _L ∈ rectangles r n, hi := by
        apply Finset.sum_le_sum
        intro L hL
        exact hhi L (Finset.mem_filter.mp hL).2
      _ = ((rectangles r n).card : ℝ) * hi := by simp

/-- Multiplicative induction; no positivity of `R` is assumed or needed. -/
theorem count_product_bounds (N : ℕ) (R a b : ℕ → ℝ)
    (hzero : R 0 = 1)
    (ha : ∀ i, i < N → 0 ≤ a i)
    (hb : ∀ i, i < N → 0 ≤ b i)
    (hstep : ∀ i, i < N →
      R i * a i ≤ R (i + 1) ∧ R (i + 1) ≤ R i * b i) :
    ∀ r, r ≤ N →
      (∏ i ∈ Finset.range r, a i) ≤ R r ∧
      R r ≤ ∏ i ∈ Finset.range r, b i := by
  intro r
  induction r with
  | zero =>
      intro _
      simp [hzero]
  | succ r ih =>
      intro hr
      have hrN : r < N := Nat.lt_of_succ_le hr
      have hi := ih (Nat.le_of_lt hrN)
      have hs := hstep r hrN
      constructor
      · calc
          (∏ i ∈ Finset.range (r + 1), a i) =
              (∏ i ∈ Finset.range r, a i) * a r := Finset.prod_range_succ _ _
          _ ≤ R r * a r := mul_le_mul_of_nonneg_right hi.1 (ha r hrN)
          _ ≤ R (r + 1) := hs.1
      · calc
          R (r + 1) ≤ R r * b r := hs.2
          _ ≤ (∏ i ∈ Finset.range r, b i) * b r :=
            mul_le_mul_of_nonneg_right hi.2 (hb r hrN)
          _ = ∏ i ∈ Finset.range (r + 1), b i := (Finset.prod_range_succ _ _).symm

/-- Uniform extension bounds give products bounding the exact public labeled count. -/
theorem latinCount_product_bounds_of_uniform (n : ℕ) (lo hi : ℕ → ℝ)
    (hlo_nonneg : ∀ r, r < n → 0 ≤ lo r)
    (hhi_nonneg : ∀ r, r < n → 0 ≤ hi r)
    (hrow : ∀ r, r < n → ∀ L : Fin r → Fin n → Fin n, Rectangle L →
      lo r ≤ ((rowExtensions L).card : ℝ) ∧
      ((rowExtensions L).card : ℝ) ≤ hi r) :
    (∏ r ∈ Finset.range n, lo r) ≤ (BookSixth.latinCount n : ℝ) ∧
    (BookSixth.latinCount n : ℝ) ≤ ∏ r ∈ Finset.range n, hi r := by
  have hzero : ((rectangles 0 n).card : ℝ) = 1 := by
    rw [rectangles_zero_card]
    norm_num
  have hstep (r : ℕ) (hr : r < n) :
      ((rectangles r n).card : ℝ) * lo r ≤ ((rectangles (r + 1) n).card : ℝ) ∧
      ((rectangles (r + 1) n).card : ℝ) ≤ ((rectangles r n).card : ℝ) * hi r :=
    rectangle_step_bounds_of_uniform (lo r) (hi r)
      (fun L hL => (hrow r hr L hL).1)
      (fun L hL => (hrow r hr L hL).2)
  have h := count_product_bounds n (fun r => ((rectangles r n).card : ℝ)) lo hi
    hzero hlo_nonneg hhi_nonneg hstep n le_rfl
  simpa only [rectangles_full_card] using h

end BookSixth.LatinBridge

namespace BookSixth.LatinBridge

theorem permanent_natCast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    (BookSixth.permanent A : ℝ) =
      Matrix.permanent (fun i j => (A i j : ℝ)) := by
  classical
  calc
    (BookSixth.permanent A : ℝ) =
        Matrix.permanent (fun i j => (A j i : ℝ)) := by
      simp only [BookSixth.permanent, Matrix.permanent, Nat.cast_sum, Nat.cast_prod]
    _ = Matrix.permanent (fun i j => (A i j : ℝ)) :=
      Matrix.permanent_transpose (fun i j => (A i j : ℝ))

theorem regular_permanent_lower
    (hLower : ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℝ),
      B ∈ doublyStochastic ℝ (Fin m) →
      (m.factorial : ℝ) / (m : ℝ) ^ m ≤ B.permanent)
    {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hrow : ∀ i, ∑ j, A i j = k)
    (hcol : ∀ j, ∑ i, A i j = k) :
    ((n.factorial : ℝ) / (n : ℝ) ^ n) * (k : ℝ) ^ n ≤
      (BookSixth.permanent A : ℝ) := by
  classical
  let AReal : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j : ℝ)
  have hrowReal (i : Fin n) : ∑ j, AReal i j = (k : ℝ) := by
    simpa only [AReal, Nat.cast_sum] using
      congrArg (fun x : ℕ => (x : ℝ)) (hrow i)
  have hcolReal (j : Fin n) : ∑ i, AReal i j = (k : ℝ) := by
    simpa only [AReal, Nat.cast_sum] using
      congrArg (fun x : ℕ => (x : ℝ)) (hcol j)
  obtain ⟨B, hB, hscale⟩ :=
    (exists_mem_doublyStochastic_eq_smul_iff (M := AReal) (s := (k : ℝ))
      (Nat.cast_nonneg k)).2
      ⟨fun i j => Nat.cast_nonneg (A i j), hrowReal, hcolReal⟩
  calc
    ((n.factorial : ℝ) / (n : ℝ) ^ n) * (k : ℝ) ^ n ≤
        B.permanent * (k : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (hLower n B hB) (pow_nonneg (Nat.cast_nonneg k) n)
    _ = (k : ℝ) ^ n * B.permanent := mul_comm _ _
    _ = AReal.permanent := by
      rw [hscale, Matrix.permanent_smul, Fintype.card_fin]
    _ = (BookSixth.permanent A : ℝ) := (permanent_natCast A).symm

theorem regular_permanent_upper
    (hUpper : ∀ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℕ),
      (∀ i j, B i j ≤ 1) → (∀ i, 0 < ∑ j, B i j) →
      (BookSixth.permanent B : ℝ) ≤
        ∏ i, ((Nat.factorial (∑ j, B i j) : ℕ) : ℝ) ^
          (1 / ((∑ j, B i j : ℕ) : ℝ)))
    {n k : ℕ} (hk : 0 < k) (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (hrow : ∀ i, ∑ j, A i j = k) :
    (BookSixth.permanent A : ℝ) ≤
      (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  classical
  have hpos (i : Fin n) : 0 < ∑ j, A i j := by
    rw [hrow i]
    exact hk
  calc
    (BookSixth.permanent A : ℝ) ≤
        ∏ _i : Fin n, (k.factorial : ℝ) ^ (1 / (k : ℝ)) := by
      simpa only [hrow] using hUpper A hA hpos
    _ = ((k.factorial : ℝ) ^ (1 / (k : ℝ))) ^ n := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg k.factorial) (1 / (k : ℝ)) n]
      congr 1
      rw [one_div, div_eq_mul_inv]
      exact mul_comm _ _

theorem regular_permanent_bounds
    (hLower : ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℝ),
      B ∈ doublyStochastic ℝ (Fin m) →
      (m.factorial : ℝ) / (m : ℝ) ^ m ≤ B.permanent)
    (hUpper : ∀ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℕ),
      (∀ i j, B i j ≤ 1) → (∀ i, 0 < ∑ j, B i j) →
      (BookSixth.permanent B : ℝ) ≤
        ∏ i, ((Nat.factorial (∑ j, B i j) : ℕ) : ℝ) ^
          (1 / ((∑ j, B i j : ℕ) : ℝ)))
    {n k : ℕ} (hk : 0 < k) (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1)
    (hrow : ∀ i, ∑ j, A i j = k)
    (hcol : ∀ j, ∑ i, A i j = k) :
    ((n.factorial : ℝ) / (n : ℝ) ^ n) * (k : ℝ) ^ n ≤
      (BookSixth.permanent A : ℝ) ∧
    (BookSixth.permanent A : ℝ) ≤
      (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  exact ⟨regular_permanent_lower hLower A hrow hcol,
    regular_permanent_upper hUpper hk A hA hrow⟩

end BookSixth.LatinBridge

namespace BookSixth.LatinBridge

private theorem descending_product_eq_Icc {M : Type*} [CommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (∏ r ∈ Finset.range n, f (n - r)) = ∏ k ∈ Finset.Icc 1 n, f k := by
  calc
    (∏ r ∈ Finset.range n, f (n - r)) =
        ∏ r ∈ Finset.range n, f (n - 1 - r + 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hrn := Finset.mem_range.mp hr
      congr 1
      omega
    _ = ∏ r ∈ Finset.range n, f (r + 1) :=
      Finset.prod_range_reflect (fun r => f (r + 1)) n
    _ = ∏ k ∈ Finset.Icc 1 n, f k := by
      simpa only [Nat.add_sub_cancel, Nat.add_comm 1,
        Finset.Ico_add_one_right_eq_Icc] using
        (Finset.prod_Ico_eq_prod_range f 1 (n + 1)).symm

theorem latin_lower_product (n : ℕ) :
    (∏ r ∈ Finset.range n,
      ((n.factorial : ℝ) / (n : ℝ)^n) * ((n-r : ℕ) : ℝ)^n) =
      (n.factorial : ℝ)^(2*n) / (n : ℝ)^(n*n) := by
  have hprod : (∏ r ∈ Finset.range n, ((n-r : ℕ) : ℝ)) =
      (n.factorial : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun m : ℕ => (m : ℝ))
        ((Nat.descFactorial_eq_prod_range n n).symm.trans (Nat.descFactorial_self n))
  calc
    (∏ r ∈ Finset.range n,
        ((n.factorial : ℝ) / (n : ℝ)^n) * ((n-r : ℕ) : ℝ)^n) =
        ((n.factorial : ℝ) / (n : ℝ)^n)^n * (n.factorial : ℝ)^n := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow, hprod]
    _ = ((n.factorial : ℝ)^n / (n : ℝ)^(n*n)) * (n.factorial : ℝ)^n := by
      rw [div_pow, ← pow_mul]
    _ = (n.factorial : ℝ)^(2*n) / (n : ℝ)^(n*n) := by
      rw [div_mul_eq_mul_div₀, ← pow_add, two_mul]

theorem latin_upper_product (n : ℕ) :
    (∏ r ∈ Finset.range n,
      ((n-r).factorial : ℝ)^((n : ℝ)/((n-r : ℕ) : ℝ))) =
      ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ)^((n : ℝ)/(k : ℝ)) :=
  descending_product_eq_Icc (fun k => (k.factorial : ℝ)^((n : ℝ)/(k : ℝ))) n

theorem latin_bounds_from_permanent_inequalities
    (hLower : ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) ℝ),
      B ∈ doublyStochastic ℝ (Fin m) →
      (m.factorial : ℝ) / (m : ℝ) ^ m ≤ B.permanent)
    (hUpper : ∀ {m : ℕ} (B : Matrix (Fin m) (Fin m) ℕ),
      (∀ i j, B i j ≤ 1) → (∀ i, 0 < ∑ j, B i j) →
      (BookSixth.permanent B : ℝ) ≤
        ∏ i, ((Nat.factorial (∑ j, B i j) : ℕ) : ℝ) ^
          (1 / ((∑ j, B i j : ℕ) : ℝ)))
    (n : ℕ) (hn : 0 < n) :
    ((n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) ≤ BookSixth.latinCount n) ∧
      ((BookSixth.latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n,
        (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) := by
  let lo : ℕ → ℝ := fun r =>
    ((n.factorial : ℝ) / (n : ℝ)^n) * ((n-r : ℕ) : ℝ)^n
  let hi : ℕ → ℝ := fun r =>
    ((n-r).factorial : ℝ)^((n : ℝ)/((n-r : ℕ) : ℝ))
  have hlo (r : ℕ) (_hr : r < n) : 0 ≤ lo r :=
    mul_nonneg
      (div_nonneg (Nat.cast_nonneg n.factorial) (pow_nonneg (Nat.cast_nonneg n) n))
      (pow_nonneg (Nat.cast_nonneg (n-r)) n)
  have hhi (r : ℕ) (_hr : r < n) : 0 ≤ hi r :=
    Real.rpow_nonneg (Nat.cast_nonneg (n-r).factorial) _
  have hrow (r : ℕ) (hr : r < n) (L : Fin r → Fin n → Fin n)
      (hL : Rectangle L) :
      lo r ≤ ((rowExtensions L).card : ℝ) ∧
      ((rowExtensions L).card : ℝ) ≤ hi r := by
    have h := regular_permanent_bounds hLower hUpper
      (Nat.sub_pos_of_lt hr) (availability L) (availability_le_one L)
      (availability_row_sum L hL) (availability_column_sum L hL)
    simpa only [lo, hi, rowExtensions_card_eq_permanent L hL] using h
  have h := latinCount_product_bounds_of_uniform n lo hi hlo hhi hrow
  simpa only [lo, hi, latin_lower_product, latin_upper_product] using h

end BookSixth.LatinBridge

open BookSixth

theorem solution (n : ℕ) (hn : 0 < n) :
    ((n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) ≤ latinCount n) ∧
      ((latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n,
        (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) := by
  exact BookSixth.LatinBridge.latin_bounds_from_permanent_inequalities
    (fun m B hB => ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional m B hB)
    (fun {m} B hB hrows => BookSixth.bregman_minc (n := m) B hB hrows)
    n hn

#print axioms solution
