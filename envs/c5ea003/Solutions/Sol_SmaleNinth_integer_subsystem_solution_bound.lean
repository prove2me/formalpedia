-- Prove2me | solution 1 for SmaleNinth.integer_subsystem_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T04:57:15.23517+00:00
-- url     : https://prove2.me/submissions/856d1808-1e19-4cbb-b3d4-d62b45c770fb

import Mathlib
import Definitions.Def_Polyhedron

open Matrix Module LinearOptimization

namespace SquareSub

/-- A matrix with linearly independent columns has a square selection of rows with
nonzero determinant. -/
lemma exists_nonsingular_rows {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}
    (B : Matrix I (Fin r) ℝ) (hcols : LinearIndependent ℝ B.col) :
    ∃ s : Fin r → I, (B.submatrix s id).det ≠ 0 := by
  classical
  have hrank : B.rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hcols, Fintype.card_fin]
  have hspanrank : finrank ℝ (Submodule.span ℝ (Set.range B.row)) = r := by
    rw [← Matrix.rank_eq_finrank_span_row, hrank]
  have hspan : Submodule.span ℝ (Set.range B.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspanrank]
    simp
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' (K := ℝ) B.row
  have hsptop : Submodule.span ℝ (Set.range (B.row ∘ a)) = ⊤ := by
    rw [hsp, hspan]
  let bas : Basis κ ℝ (Fin r → ℝ) := Basis.mk hli (by rw [hsptop])
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex bas
  let e : κ ≃ Fin r := bas.indexEquiv (Pi.basisFun ℝ (Fin r))
  refine ⟨a ∘ e.symm, ?_⟩
  set N : Matrix (Fin r) (Fin r) ℝ := B.submatrix (a ∘ e.symm) id with hN
  have hNrow : N.row = (B.row ∘ a) ∘ e.symm := rfl
  have hNli : LinearIndependent ℝ N.row := by
    rw [hNrow]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit N := Matrix.linearIndependent_rows_iff_isUnit.1 hNli
  exact isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det N).1 hunit)

variable {m n : ℕ}

/-- Zero coordinates of `y`. -/
noncomputable def zeros (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => y j = 0)

lemma mem_zeros {y : Fin n → ℝ} {j : Fin n} : j ∈ zeros y ↔ y j = 0 := by
  classical
  simp [zeros]

/-- A solution of the subsystem whose set of zero coordinates is as large as possible. -/
lemma exists_max_zeros (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (I : Finset (Fin m)) (x : Fin n → ℝ)
    (hx : ∀ i ∈ I, A.mulVec x i = b i) :
    ∃ y : Fin n → ℝ,
      (∀ i ∈ I, A.mulVec y i = b i) ∧
      ∀ z : Fin n → ℝ,
        (∀ i ∈ I, A.mulVec z i = b i) → (zeros z).card ≤ (zeros y).card := by
  classical
  set S : Set ℕ :=
    {k | ∃ y : Fin n → ℝ,
      (∀ i ∈ I, A.mulVec y i = b i) ∧ (zeros y).card = k} with hS
  have hSne : S.Nonempty := ⟨_, x, hx, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro k ⟨z, -, rfl⟩
    simpa using (zeros z).card_le_univ
  obtain ⟨y, hy, hcard⟩ := Nat.sSup_mem hSne hSbdd
  exact ⟨y, hy, fun z hz => hcard ▸ le_csSup hSbdd ⟨z, hz, rfl⟩⟩

/-- Spread a vector indexed by the chosen columns back over all coordinates. -/
noncomputable def spread {r : ℕ} (col : Fin r → Fin n) (g : Fin r → ℝ) :
    Fin n → ℝ :=
  fun j => ∑ k, if col k = j then g k else 0

lemma spread_col {r : ℕ} {col : Fin r → Fin n} (hcol : Function.Injective col)
    (g : Fin r → ℝ) (k₀ : Fin r) : spread col g (col k₀) = g k₀ := by
  classical
  unfold spread
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (hcol h) hk
  · simp

lemma spread_not_mem {r : ℕ} {col : Fin r → Fin n} (g : Fin r → ℝ) {j : Fin n}
    (hj : j ∉ Set.range col) : spread col g j = 0 := by
  classical
  unfold spread
  refine Finset.sum_eq_zero fun k _ => ?_
  have : col k ≠ j := fun h => hj ⟨k, h⟩
  simp [this]

lemma mulVec_spread {r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (col : Fin r → Fin n)
    (g : Fin r → ℝ) (i : Fin m) :
    A.mulVec (spread col g) i = ∑ k, A i (col k) * g k := by
  classical
  unfold Matrix.mulVec spread
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (col k)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

end SquareSub

open SquareSub

theorem SmaleNinth.exists_square_subsystem_port {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (I : Finset (Fin m)) (x : Fin n → ℝ)
    (hx : ∀ i ∈ I, A.mulVec x i = b i) :
    ∃ (r : ℕ) (y : Fin n → ℝ) (row : Fin r → Fin m) (col : Fin r → Fin n),
      (∀ i ∈ I, A.mulVec y i = b i) ∧
      r ≤ n ∧
      (A.submatrix row col).det ≠ 0 ∧
      (A.submatrix row col).mulVec (fun k => y (col k)) = (fun k => b (row k)) ∧
      (∀ j, j ∉ Set.range col → y j = 0) := by
  classical
  obtain ⟨y, hy, hmax⟩ := exists_max_zeros A b I x hx
  set T : Finset (Fin n) := (zeros y)ᶜ with hT
  set r : ℕ := T.card with hr
  have hrn : r ≤ n := by
    simpa [hr] using T.card_le_univ
  set ord := T.orderIsoOfFin (rfl : T.card = r) with hord
  set col : Fin r → Fin n := fun k => (ord k : Fin n) with hcoldef
  have hcolmem : ∀ k, col k ∈ T := fun k => (ord k).2
  have hcolinj : Function.Injective col :=
    fun k1 k2 h => ord.injective (Subtype.ext h)
  have hrange : Set.range col = (↑T : Set (Fin n)) := by
    ext j
    constructor
    · rintro ⟨k, rfl⟩
      exact hcolmem k
    · intro hj
      exact ⟨ord.symm ⟨j, hj⟩, by simp [hcoldef]⟩
  have hyzero : ∀ j, j ∉ Set.range col → y j = 0 := by
    intro j hj
    rw [hrange] at hj
    have hjz : j ∈ zeros y := by
      by_contra hc
      exact hj (by simp [hT, hc])
    exact mem_zeros.1 hjz
  have hynz : ∀ k, y (col k) ≠ 0 := by
    intro k hc
    have := hcolmem k
    rw [hT, Finset.mem_compl] at this
    exact this (mem_zeros.2 hc)
  have hyspread : y = spread col (fun k => y (col k)) := by
    funext j
    by_cases hj : j ∈ Set.range col
    · obtain ⟨k, rfl⟩ := hj
      rw [spread_col hcolinj]
    · rw [spread_not_mem _ hj, hyzero j hj]
  set B : Matrix {i // i ∈ I} (Fin r) ℝ := fun i k => A i.1 (col k) with hB
  have hindep : LinearIndependent ℝ B.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    by_contra hgk
    have hAv : ∀ i ∈ I, A.mulVec (spread col g) i = 0 := by
      intro i hi
      rw [mulVec_spread]
      have h := congrFun hg ⟨i, hi⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
      have h2 : ∑ xk, g xk * A i (col xk) = 0 := h
      calc
        ∑ k', A i (col k') * g k' =
            ∑ k', g k' * A i (col k') := by
              exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = 0 := h2
    set t : ℝ := -(y (col k)) / g k with ht
    set z : Fin n → ℝ := y + t • spread col g with hz
    have hzsol : ∀ i ∈ I, A.mulVec z i = b i := by
      intro i hi
      rw [hz]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hAv i hi, hy i hi, mul_zero, add_zero]
    have hsub : zeros y ⊆ zeros z := by
      intro j hj
      have hy0 : y j = 0 := mem_zeros.1 hj
      have hjnr : j ∉ Set.range col := by
        rw [hrange]
        intro hc
        rw [hT, Finset.mem_coe, Finset.mem_compl] at hc
        exact hc hj
      refine mem_zeros.2 ?_
      simp [hz, hy0, spread_not_mem _ hjnr]
    have hnew : col k ∈ zeros z := by
      refine mem_zeros.2 ?_
      simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        spread_col hcolinj, ht]
      field_simp
      ring
    have hnotold : col k ∉ zeros y := by
      intro hc
      exact hynz k (mem_zeros.1 hc)
    have hlt : (zeros y).card < (zeros z).card :=
      Finset.card_lt_card ⟨hsub, fun hc => hnotold (hc hnew)⟩
    exact absurd (hmax z hzsol) (by omega)
  obtain ⟨s, hs⟩ := exists_nonsingular_rows B hindep
  set row : Fin r → Fin m := fun k => (s k).1 with hrow
  have hsubeq : A.submatrix row col = B.submatrix s id := by
    ext k j
    rfl
  refine ⟨r, y, row, col, hy, hrn, by rw [hsubeq]; exact hs, ?_, hyzero⟩
  funext k
  have h1 :
      (A.submatrix row col).mulVec (fun j => y (col j)) k =
        ∑ j, A (row k) (col j) * y (col j) := by
    simp [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [h1, ← mulVec_spread A col (fun j => y (col j)) (row k), ← hyspread]
  exact hy (row k) (s k).2

open Finset

namespace CramerAux

theorem det_bound {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : ∀ i j, |M i j| ≤ (U : ℤ)) :
    |M.det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| ≤ (U : ℤ) ^ r := by
    intro σ
    have h1 :
        |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| =
          |∏ i, M (σ i) i| := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, abs_neg]
    rw [h1, Finset.abs_prod]
    calc
      ∏ i, |M (σ i) i| ≤ ∏ _i : Fin r, (U : ℤ) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hM _ _)
      _ = (U : ℤ) ^ r := by simp
  refine le_trans (Finset.sum_le_sum (fun σ _ => hterm σ)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

end CramerAux

open CramerAux

theorem SmaleNinth.cramer_solution_bound_port {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℤ)
    (hM : ∀ i j, |M i j| ≤ (U : ℤ)) (hv : ∀ i, |v i| ≤ (U : ℤ))
    (hdet : M.det ≠ 0)
    (z : Fin r → ℝ)
    (hz : (M.map (Int.cast : ℤ → ℝ)).mulVec z = fun i => ((v i : ℤ) : ℝ)) :
    ∀ j, |z j| ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := by
  classical
  set Mr : Matrix (Fin r) (Fin r) ℝ := M.map (Int.cast : ℤ → ℝ) with hMr
  set vr : Fin r → ℝ := fun i => ((v i : ℤ) : ℝ) with hvr
  have hdetMr : Mr.det = ((M.det : ℤ) : ℝ) := (Int.cast_det M).symm
  have hdetne : Mr.det ≠ 0 := by
    rw [hdetMr]
    exact_mod_cast hdet
  have hkey : Mr.det • z = Mr.cramer vr := by
    have h1 : Mr.mulVec (Mr.cramer vr) = Mr.det • vr :=
      Matrix.mulVec_cramer Mr vr
    have h2 : Mr.mulVec (Mr.det • z) = Mr.det • vr := by
      rw [Matrix.mulVec_smul, hz]
    have hunit : IsUnit Mr :=
      (Matrix.isUnit_iff_isUnit_det Mr).2 (isUnit_iff_ne_zero.2 hdetne)
    have hinj : Function.Injective Mr.mulVec :=
      Matrix.mulVec_injective_of_isUnit hunit
    exact hinj (h2.trans h1.symm)
  intro j
  have hcol : Mr.cramer vr j = (((M.updateCol j v).det : ℤ) : ℝ) := by
    rw [Matrix.cramer_apply]
    have :
        Mr.updateCol j vr = (M.updateCol j v).map (Int.cast : ℤ → ℝ) := by
      ext a c
      by_cases hc : c = j <;>
        simp [hc, hMr, hvr]
    rw [this]
    exact (Int.cast_det _).symm
  have hzj :
      ((M.det : ℤ) : ℝ) * z j =
        (((M.updateCol j v).det : ℤ) : ℝ) := by
    have := congrFun hkey j
    simpa [hdetMr, hcol] using this
  have hnum :
      |(M.updateCol j v).det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by
    refine det_bound U _ fun a c => ?_
    by_cases hc : c = j <;>
      simp [hc, hv a, hM a c]
  have hden : (1 : ℝ) ≤ |((M.det : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |M.det| := Int.one_le_abs (by exact_mod_cast hdet)
    exact_mod_cast this
  have habs :
      |((M.det : ℤ) : ℝ)| * |z j| ≤
        (r.factorial : ℝ) * (U : ℝ) ^ r := by
    rw [← abs_mul, hzj]
    have hcast :
        |(((M.updateCol j v).det : ℤ) : ℝ)| ≤
          (((r.factorial : ℤ) * (U : ℤ) ^ r : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hnum
    simpa using hcast
  calc
    |z j| = 1 * |z j| := (one_mul _).symm
    _ ≤ |((M.det : ℤ) : ℝ)| * |z j| :=
      mul_le_mul_of_nonneg_right hden (abs_nonneg _)
    _ ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := habs

namespace SubAux

lemma submatrix_map {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (row : Fin r → Fin m) (col : Fin r → Fin n) :
    (A.map (Int.cast : ℤ → ℝ)).submatrix row col =
      (A.submatrix row col).map (Int.cast : ℤ → ℝ) := by
  ext k j
  simp [Matrix.submatrix_apply, Matrix.map_apply]

end SubAux

open SubAux

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (I : Finset (Fin m))
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (x : Fin n → ℝ)
    (hx : ∀ i ∈ I,
      (A.map (Int.cast : ℤ → ℝ)).mulVec x i = (b i : ℝ)) :
    ∃ y : Fin n → ℝ,
      (∀ i ∈ I,
        (A.map (Int.cast : ℤ → ℝ)).mulVec y i = (b i : ℝ)) ∧
      (∀ j, |y j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n) := by
  classical
  obtain ⟨r, y, row, col, hsol, hrn, hdet, hmul, hzero⟩ :=
    SmaleNinth.exists_square_subsystem_port
      (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)) I x hx
  refine ⟨y, hsol, ?_⟩
  set M : Matrix (Fin r) (Fin r) ℤ := A.submatrix row col with hM
  set v : Fin r → ℤ := fun k => b (row k) with hv
  have hmapsub :
      (A.map (Int.cast : ℤ → ℝ)).submatrix row col =
        M.map (Int.cast : ℤ → ℝ) :=
    submatrix_map A row col
  have hdetM : M.det ≠ 0 := by
    intro hc
    rw [hmapsub] at hdet
    exact hdet (by rw [← Int.cast_det, hc]; norm_num)
  have hMbd : ∀ i j, |M i j| ≤ (U : ℤ) := fun i j => hA _ _
  have hvbd : ∀ i, |v i| ≤ (U : ℤ) := fun i => hb _
  have hmul' :
      (M.map (Int.cast : ℤ → ℝ)).mulVec (fun k => y (col k)) =
        fun k => ((v k : ℤ) : ℝ) := by
    rw [← hmapsub]
    exact hmul
  have hcr :=
    SmaleNinth.cramer_solution_bound_port U M v hMbd hvbd hdetM _ hmul'
  have hmono :
      (r.factorial : ℝ) * (U : ℝ) ^ r ≤
        (n.factorial : ℝ) * (U : ℝ) ^ n := by
    have h1 : (r.factorial : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hrn
    have h2 : (U : ℝ) ^ r ≤ (U : ℝ) ^ n := by
      refine pow_le_pow_right₀ ?_ hrn
      exact_mod_cast hU
    have hpos : (0 : ℝ) ≤ (U : ℝ) ^ r := by positivity
    exact mul_le_mul h1 h2 hpos (by positivity)
  intro j
  by_cases hj : j ∈ Set.range col
  · obtain ⟨k, rfl⟩ := hj
    exact le_trans (hcr k) hmono
  · rw [hzero j hj, abs_zero]
    positivity
