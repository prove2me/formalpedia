-- Prove2me | solution 1 for VectorSpaceOpt.riesz_representation_C_nbv_open
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T04:08:57.716881+00:00
-- url     : https://prove2.me/submissions/de173c05-eb67-44cd-8958-43337a54b49b

import Mathlib
import Definitions.Def_VectorSpaceOpt_is_nbv_open
open Set Filter Topology


open Set Filter Topology

namespace RS

/-- `IsPart a b n t` says `t 0 = a`, `t n = b` and `t` is nondecreasing on `0, …, n`. -/
structure IsPart (a b : ℝ) (n : ℕ) (t : ℕ → ℝ) : Prop where
  left : t 0 = a
  right : t n = b
  step : ∀ i < n, t i ≤ t (i + 1)

/-- Tags subordinate to a partition. -/
def IsTag (n : ℕ) (t ξ : ℕ → ℝ) : Prop := ∀ i < n, t i ≤ ξ i ∧ ξ i ≤ t (i + 1)

/-- The Riemann–Stieltjes sum of a tagged partition. -/
noncomputable def rsSum (x v : ℝ → ℝ) (n : ℕ) (t ξ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))

/-- A partition is monotone on the index range. -/
theorem IsPart.mono {a b : ℝ} {n : ℕ} {t : ℕ → ℝ} (h : IsPart a b n t) :
    ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
  intro i j hij hjn
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.1 hlt) (le_trans (Nat.le_succ k) hjn))
        (h.step k (lt_of_lt_of_le (Nat.lt_succ_self k) hjn))
    · have : i = k + 1 := le_antisymm hij hge
      rw [this]

/-- Partition points lie in `[a, b]`. -/
theorem IsPart.mem {a b : ℝ} {n : ℕ} {t : ℕ → ℝ} (h : IsPart a b n t) :
    ∀ i ≤ n, t i ∈ Set.Icc a b := by
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [← h.left]; exact h.mono 0 i (Nat.zero_le i) hi
  · rw [← h.right]; exact h.mono i n hi le_rfl

/-- Telescoping over an `Ico` block. -/
theorem sum_Ico_telescope (F : ℕ → ℝ) : ∀ p q : ℕ, p ≤ q →
    (∑ i ∈ Finset.Ico p q, (F (i + 1) - F i)) = F q - F p := by
  intro p q hpq
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring

/-- Regrouping a range sum along a monotone index map. -/
theorem sum_blocks (g : ℕ → ℝ) (σ : ℕ → ℕ) (hσ : Monotone σ) :
    ∀ k : ℕ, (∑ j ∈ Finset.range k, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)), g i)
      = ∑ i ∈ Finset.Ico (σ 0) (σ k), g i := by
  intro k
  induction k with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ, ih]
    exact Finset.sum_Ico_consecutive g (hσ (Nat.zero_le l)) (hσ (Nat.le_succ l))

/-- The variation bound for a finite monotone sample. -/
theorem varsum_le {v : ℝ → ℝ} {a b : ℝ} (hv : BoundedVariationOn v (Set.Icc a b))
    {N : ℕ} {u : ℕ → ℝ} (hmono : ∀ i j, i ≤ j → j ≤ N → u i ≤ u j)
    (hmem : ∀ i ≤ N, u i ∈ Set.Icc a b) :
    (∑ i ∈ Finset.range N, |v (u (i + 1)) - v (u i)|)
      ≤ VectorSpaceOpt_total_variation v a b := by
  have hmonoOn : MonotoneOn u (Set.Iic N) := by
    intro i hi j hj hij
    exact hmono i j hij hj
  have hkey := eVariationOn.sum_le_of_monotoneOn_Iic (f := v) (s := Set.Icc a b)
    hmonoOn (fun i hi => hmem i hi)
  have hedist : ∀ i : ℕ, edist (v (u (i + 1))) (v (u i))
      = ENNReal.ofReal |v (u (i + 1)) - v (u i)| := by
    intro i
    rw [edist_dist, Real.dist_eq]
  rw [Finset.sum_congr rfl (fun i _ => hedist i), ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => abs_nonneg _)] at hkey
  rw [VectorSpaceOpt_total_variation]
  rw [← ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
  exact ENNReal.toReal_mono hv hkey

/-- Comparing a tagged sum with a tagged sum over a refinement of the same partition. -/
theorem rs_refine {x v : ℝ → ℝ} {a b : ℝ} (hv : BoundedVariationOn v (Set.Icc a b))
    {ω : ℝ} (hωnn : 0 ≤ ω) {n N : ℕ} {t ξ u η : ℕ → ℝ} {σ : ℕ → ℕ}
    (ht : IsPart a b n t) (hξ : IsTag n t ξ)
    (hu : IsPart a b N u) (hη : IsTag N u η)
    (hσ : Monotone σ) (hσ0 : σ 0 = 0) (hσn : σ n = N)
    (hut : ∀ j ≤ n, u (σ j) = t j)
    (hclose : ∀ j < n, ∀ s₁ s₂ : ℝ, t j ≤ s₁ → s₁ ≤ t (j + 1) → t j ≤ s₂ → s₂ ≤ t (j + 1) →
       |x s₁ - x s₂| ≤ ω) :
    |rsSum x v n t ξ - rsSum x v N u η| ≤ ω * VectorSpaceOpt_total_variation v a b := by
  have hg : ∀ j, σ j ≤ σ (j + 1) := fun j => hσ (Nat.le_succ j)
  have hσle : ∀ j, j ≤ n → σ j ≤ N := fun j hj => hσn ▸ hσ hj
  have hA : rsSum x v n t ξ
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)),
          x (ξ j) * (v (u (i + 1)) - v (u i)) := by
    rw [rsSum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j < n := Finset.mem_range.1 hj
    rw [← Finset.mul_sum, sum_Ico_telescope (fun i => v (u i)) _ _ (hg j),
      hut j (le_of_lt hjn), hut (j + 1) hjn]
  have hB : rsSum x v N u η
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)),
          x (η i) * (v (u (i + 1)) - v (u i)) := by
    rw [sum_blocks (fun i => x (η i) * (v (u (i + 1)) - v (u i))) σ hσ n, hσ0, hσn, rsSum,
      Finset.range_eq_Ico]
  have hdiff : rsSum x v n t ξ - rsSum x v N u η
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)),
          (x (ξ j) - x (η i)) * (v (u (i + 1)) - v (u i)) := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hdiff]
  have hbound : ∀ j ∈ Finset.range n,
      |∑ i ∈ Finset.Ico (σ j) (σ (j + 1)), (x (ξ j) - x (η i)) * (v (u (i + 1)) - v (u i))|
        ≤ ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)), ω * |v (u (i + 1)) - v (u i)| := by
    intro j hj
    have hjn : j < n := Finset.mem_range.1 hj
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    have hiN : i + 1 ≤ N := le_trans hi2 (hσle (j + 1) hjn)
    have hiN' : i ≤ N := le_trans (Nat.le_succ i) hiN
    have hlow : t j ≤ u i := by
      rw [← hut j (le_of_lt hjn)]; exact hu.mono _ _ hi1 hiN'
    have hhigh : u (i + 1) ≤ t (j + 1) := by
      rw [← hut (j + 1) hjn]; exact hu.mono _ _ hi2 (hσle (j + 1) hjn)
    obtain ⟨hη1, hη2⟩ := hη i (lt_of_lt_of_le hi2 (hσle (j + 1) hjn))
    obtain ⟨hξ1, hξ2⟩ := hξ j hjn
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact hclose j hjn (ξ j) (η i) hξ1 hξ2 (le_trans hlow hη1) (le_trans hη2 hhigh)
  calc |∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)),
          (x (ξ j) - x (η i)) * (v (u (i + 1)) - v (u i))|
      ≤ ∑ j ∈ Finset.range n,
          |∑ i ∈ Finset.Ico (σ j) (σ (j + 1)), (x (ξ j) - x (η i)) * (v (u (i + 1)) - v (u i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (σ j) (σ (j + 1)), ω * |v (u (i + 1)) - v (u i)| :=
        Finset.sum_le_sum hbound
    _ = ω * ∑ i ∈ Finset.range N, |v (u (i + 1)) - v (u i)| := by
        simp only [← Finset.mul_sum]
        congr 1
        rw [sum_blocks (fun i => |v (u (i + 1)) - v (u i)|) σ hσ n, hσ0, hσn,
          Finset.range_eq_Ico]
    _ ≤ ω * VectorSpaceOpt_total_variation v a b :=
        mul_le_mul_of_nonneg_left (varsum_le hv hu.mono hu.mem) hωnn


/-- The `i`-th point of a finite set of reals, listed in increasing order. -/
noncomputable def mPart (W : Finset ℝ) (b : ℝ) (i : ℕ) : ℝ :=
  if h : i < W.card then W.orderEmbOfFin (rfl : W.card = W.card) ⟨i, h⟩ else b

/-- The position of a member of `W` in that increasing list. -/
noncomputable def mIdx (W : Finset ℝ) (y : ℝ) : ℕ :=
  if h : y ∈ W then (((W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨y, h⟩ : Fin W.card) : ℕ)
  else 0

theorem mIdx_lt {W : Finset ℝ} {y : ℝ} (hy : y ∈ W) : mIdx W y < W.card := by
  rw [mIdx, dif_pos hy]
  exact (((W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨y, hy⟩ : Fin W.card)).2

theorem mPart_mIdx {W : Finset ℝ} {b y : ℝ} (hy : y ∈ W) : mPart W b (mIdx W y) = y := by
  have hval : mIdx W y
      = (((W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨y, hy⟩ : Fin W.card) : ℕ) := by
    rw [mIdx, dif_pos hy]
  have hlt : mIdx W y < W.card := mIdx_lt hy
  rw [mPart, dif_pos hlt]
  have hfin : (⟨mIdx W y, hlt⟩ : Fin W.card)
      = (W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨y, hy⟩ := Fin.ext hval
  rw [hfin, ← Finset.coe_orderIsoOfFin_apply]
  simp

theorem mIdx_mono {W : Finset ℝ} {y z : ℝ} (hy : y ∈ W) (hz : z ∈ W) (h : y ≤ z) :
    mIdx W y ≤ mIdx W z := by
  rw [mIdx, dif_pos hy, mIdx, dif_pos hz]
  have : ((W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨y, hy⟩ : Fin W.card)
      ≤ (W.orderIsoOfFin (rfl : W.card = W.card)).symm ⟨z, hz⟩ := by
    apply OrderIso.monotone
    exact h
  exact this

theorem mPart_mono {W : Finset ℝ} {b : ℝ} {i j : ℕ} (hij : i ≤ j) (hj : j < W.card) :
    mPart W b i ≤ mPart W b j := by
  have hi : i < W.card := lt_of_le_of_lt hij hj
  rw [mPart, dif_pos hi, mPart, dif_pos hj]
  exact (W.orderEmbOfFin (rfl : W.card = W.card)).monotone (by exact hij)

theorem mPart_mem {W : Finset ℝ} {b : ℝ} {i : ℕ} (hi : i < W.card) : mPart W b i ∈ W := by
  rw [mPart, dif_pos hi]
  exact Finset.orderEmbOfFin_mem _ _ _


theorem mPart_strictMono {W : Finset ℝ} {b : ℝ} {i j : ℕ} (hij : i < j) (hj : j < W.card) :
    mPart W b i < mPart W b j := by
  have hi : i < W.card := lt_trans hij hj
  rw [mPart, dif_pos hi, mPart, dif_pos hj]
  exact (W.orderEmbOfFin (rfl : W.card = W.card)).strictMono (by exact hij)

/-- Two tagged partitions of mesh at most `δ` have Riemann–Stieltjes sums within `2ω·TV`. -/
theorem rs_compare {x v : ℝ → ℝ} {a b : ℝ}
    (hv : BoundedVariationOn v (Set.Icc a b))
    {ω δ : ℝ} (hωnn : 0 ≤ ω)
    (hω : ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b, |p - q| ≤ δ → |x p - x q| ≤ ω)
    {n m : ℕ} {t ξ s η : ℕ → ℝ}
    (ht : IsPart a b n t) (hξ : IsTag n t ξ) (htm : ∀ i < n, t (i + 1) - t i ≤ δ)
    (hs : IsPart a b m s) (hη : IsTag m s η) (hsm : ∀ i < m, s (i + 1) - s i ≤ δ) :
    |rsSum x v n t ξ - rsSum x v m s η|
      ≤ 2 * ω * VectorSpaceOpt_total_variation v a b := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : Finset ℝ,
      W = ((Finset.range (n + 1)).image t) ∪ ((Finset.range (m + 1)).image s) := ⟨_, rfl⟩
  have hta : ∀ j, j ≤ n → t j ∈ W := by
    intro j hj
    rw [hW]
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩)
  have hsa : ∀ j, j ≤ m → s j ∈ W := by
    intro j hj
    rw [hW]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩)
  have hWsub : ∀ y ∈ W, y ∈ Set.Icc a b := by
    intro y hy
    rw [hW, Finset.mem_union] at hy
    rcases hy with hy | hy
    · obtain ⟨j, hj, hjy⟩ := Finset.mem_image.1 hy
      rw [← hjy]
      exact ht.mem j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    · obtain ⟨j, hj, hjy⟩ := Finset.mem_image.1 hy
      rw [← hjy]
      exact hs.mem j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have haW : a ∈ W := by rw [← ht.left]; exact hta 0 (Nat.zero_le n)
  have hbW : b ∈ W := by rw [← ht.right]; exact hta n le_rfl
  have hcard : 0 < W.card := Finset.card_pos.2 ⟨a, haW⟩
  obtain ⟨N, hN⟩ : ∃ N, N = W.card - 1 := ⟨_, rfl⟩
  have hNc : N < W.card := by omega
  have hNsucc : N + 1 = W.card := by omega
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = mPart W b := ⟨_, rfl⟩
  have humem : ∀ i, i < W.card → u i ∈ W := by intro i hi; rw [hu]; exact mPart_mem hi
  have hidxa : mIdx W a = 0 := by
    by_contra hne
    have hpos : 0 < mIdx W a := Nat.pos_of_ne_zero hne
    have h1 : mPart W b 0 < mPart W b (mIdx W a) := mPart_strictMono hpos (mIdx_lt haW)
    rw [mPart_mIdx haW] at h1
    exact absurd (hWsub _ (mPart_mem hcard)).1 (not_le.2 h1)
  have hidxb : mIdx W b = N := by
    by_contra hne
    have hlt : mIdx W b < N := by have := mIdx_lt hbW; omega
    have h1 : mPart W b (mIdx W b) < mPart W b N := mPart_strictMono hlt hNc
    rw [mPart_mIdx hbW] at h1
    exact absurd (hWsub _ (mPart_mem hNc)).2 (not_le.2 h1)
  have hup : IsPart a b N u := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hu, ← hidxa, mPart_mIdx haW]
    · rw [hu, ← hidxb, mPart_mIdx hbW]
    · intro i hi
      rw [hu]
      exact mPart_mono (Nat.le_succ i) (by omega)
  have hutag : IsTag N u u := fun i hi => ⟨le_rfl, by rw [hu]; exact mPart_mono (Nat.le_succ i) (by omega)⟩
  -- the two index maps
  have key : ∀ (k : ℕ) (w ζ : ℕ → ℝ), IsPart a b k w → IsTag k w ζ →
      (∀ i < k, w (i + 1) - w i ≤ δ) → (∀ j, j ≤ k → w j ∈ W) →
      |rsSum x v k w ζ - rsSum x v N u u| ≤ ω * VectorSpaceOpt_total_variation v a b := by
    intro k w ζ hw hζ hwm hwW
    obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℕ, σ = fun j => mIdx W (w (min j k)) := ⟨_, rfl⟩
    have hσmono : Monotone σ := by
      intro p q hpq
      rw [hσdef]
      refine mIdx_mono (hwW _ (min_le_right _ _)) (hwW _ (min_le_right _ _)) ?_
      exact hw.mono _ _ (min_le_min hpq le_rfl) (min_le_right _ _)
    have hσ0 : σ 0 = 0 := by rw [hσdef]; simp only [Nat.zero_min]; rw [hw.left, hidxa]
    have hσk : σ k = N := by rw [hσdef]; simp only [min_self]; rw [hw.right, hidxb]
    have hut : ∀ j, j ≤ k → u (σ j) = w j := by
      intro j hj
      rw [hσdef, hu]
      simp only [min_eq_left hj]
      exact mPart_mIdx (hwW j hj)
    refine rs_refine hv hωnn hw hζ hup hutag hσmono hσ0 hσk hut ?_
    intro j hj s₁ s₂ h1 h2 h3 h4
    have hmj : w j ∈ Set.Icc a b := hw.mem j (le_of_lt hj)
    have hmj1 : w (j + 1) ∈ Set.Icc a b := hw.mem (j + 1) hj
    refine hω s₁ ⟨le_trans hmj.1 h1, le_trans h2 hmj1.2⟩ s₂ ⟨le_trans hmj.1 h3, le_trans h4 hmj1.2⟩ ?_
    have := hwm j hj
    rw [abs_le]
    constructor <;> linarith
  have h1 := key n t ξ ht hξ htm hta
  have h2 := key m s η hs hη hsm hsa
  have htri : |rsSum x v n t ξ - rsSum x v m s η|
      ≤ |rsSum x v n t ξ - rsSum x v N u u| + |rsSum x v N u u - rsSum x v m s η| := by
    have := abs_sub_abs_le_abs_sub (rsSum x v n t ξ) (rsSum x v m s η)
    calc |rsSum x v n t ξ - rsSum x v m s η|
        = |(rsSum x v n t ξ - rsSum x v N u u) + (rsSum x v N u u - rsSum x v m s η)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_sub_comm (rsSum x v N u u)] at htri
  linarith


/-! ### Uniform partitions -/

/-- The uniform partition of `[a,b]` into `k` pieces, truncated at `b`. -/
noncomputable def unif (a b : ℝ) (k : ℕ) (i : ℕ) : ℝ := min (a + i * (b - a) / k) b

theorem unif_isPart {a b : ℝ} (hab : a ≤ b) {k : ℕ} (hk : 0 < k) :
    IsPart a b k (unif a b k) := by
  have hk' : (k : ℝ) ≠ 0 := (Nat.cast_pos.2 hk).ne'
  have hd : 0 ≤ (b - a) / k := by
    apply div_nonneg (by linarith)
    exact Nat.cast_nonneg k
  refine ⟨?_, ?_, ?_⟩
  · simp only [unif, Nat.cast_zero, zero_mul, zero_div, add_zero]
    exact min_eq_left hab
  · have : a + (k : ℝ) * (b - a) / k = b := by field_simp; ring
    simp only [unif, this]
    exact min_self b
  · intro i hi
    simp only [unif]
    refine min_le_min ?_ le_rfl
    have : ((i : ℝ) + 1) * (b - a) / k = (i : ℝ) * (b - a) / k + (b - a) / k := by ring
    push_cast
    rw [this]
    linarith

theorem unif_mesh {a b : ℝ} (hab : a ≤ b) {k : ℕ} (hk : 0 < k) (i : ℕ) :
    unif a b k (i + 1) - unif a b k i ≤ (b - a) / k := by
  have hd : 0 ≤ (b - a) / k := by
    apply div_nonneg (by linarith); exact Nat.cast_nonneg k
  have hstep : (a + ((i : ℝ) + 1) * (b - a) / k) = (a + (i : ℝ) * (b - a) / k) + (b - a) / k := by
    ring
  simp only [unif]
  push_cast
  rw [hstep]
  rcases le_total (a + (i : ℝ) * (b - a) / k) b with h | h
  · rw [min_eq_left h]
    have := min_le_left (a + (i : ℝ) * (b - a) / k + (b - a) / k) b
    linarith
  · rw [min_eq_right h]
    have := min_le_right (a + (i : ℝ) * (b - a) / k + (b - a) / k) b
    linarith

/-! ### Existence of the Riemann–Stieltjes integral -/

theorem rs_exists {x v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : BoundedVariationOn v (Set.Icc a b))
    (hx : ∀ ε > 0, ∃ δ > 0, ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b,
      |p - q| ≤ δ → |x p - x q| ≤ ε) :
    ∃ I : ℝ, VectorSpaceOpt_is_rs_integral x v a b I := by
  classical
  obtain ⟨V, hV⟩ : ∃ V, V = VectorSpaceOpt_total_variation v a b := ⟨_, rfl⟩
  have hVnn : 0 ≤ V := by rw [hV, VectorSpaceOpt_total_variation]; exact ENNReal.toReal_nonneg
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℕ → ℝ,
      ω = fun k : ℕ => (1 / ((k : ℝ) + 1)) / (2 * (V + 1)) := ⟨_, rfl⟩
  have hωpos : ∀ k, 0 < ω k := by
    intro k; simp only [hωdef]
    apply div_pos (by positivity) (by linarith)
  have hωbound : ∀ k, 2 * ω k * V ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    simp only [hωdef]
    have h1 : (0:ℝ) < 2 * (V + 1) := by linarith
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hc : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have key : 2 * (1 / ((k : ℝ) + 1) / (2 * (V + 1))) * V
        = (1 / ((k : ℝ) + 1)) * (2 * V / (2 * (V + 1))) := by
      field_simp

    rw [key]
    have h2 : 2 * V / (2 * (V + 1)) ≤ 1 := by
      rw [div_le_one h1]; linarith
    calc (1 / ((k : ℝ) + 1)) * (2 * V / (2 * (V + 1))) ≤ (1 / ((k : ℝ) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left h2 hc.le
      _ = 1 / ((k : ℝ) + 1) := by ring
  choose d hdpos hdspec using fun k => hx (ω k) (hωpos k)
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ,
      D = fun k : ℕ => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one d := ⟨_, rfl⟩
  have hDpos : ∀ k, 0 < D k := by
    intro k; simp only [hDdef]
    exact (Finset.lt_inf'_iff _).2 (fun j _ => hdpos j)
  have hDle : ∀ k j, j ≤ k → D k ≤ d j := by
    intro k j hjk; simp only [hDdef]
    exact Finset.inf'_le _ (Finset.mem_range.2 (by omega))
  have hDanti : ∀ k l, k ≤ l → D l ≤ D k := by
    intro k l hkl
    simp only [hDdef]
    refine (Finset.le_inf'_iff _ _).2 (fun j hj => ?_)
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hres := hDle l j (le_trans hjk hkl)
    simpa only [hDdef] using hres
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℕ, N = fun k : ℕ => ⌈(b - a) / D k⌉₊ + 1 := ⟨_, rfl⟩
  have hNpos : ∀ k, 0 < N k := by intro k; simp only [hNdef]; omega
  have hNmesh : ∀ k, (b - a) / (N k : ℝ) < D k := by
    intro k
    have h1 : (b - a) / D k ≤ (⌈(b - a) / D k⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(b - a) / D k⌉₊ : ℝ)) < (N k : ℝ) := by
      simp only [hNdef]; push_cast; linarith
    have h3 : (b - a) / D k < (N k : ℝ) := lt_of_le_of_lt h1 h2
    have h4 : (0:ℝ) < (N k : ℝ) := by exact_mod_cast hNpos k
    rw [div_lt_iff₀ h4]
    rw [div_lt_iff₀ (hDpos k)] at h3
    linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ,
      S = fun k : ℕ => rsSum x v (N k) (unif a b (N k)) (unif a b (N k)) := ⟨_, rfl⟩
  have hunifTag : ∀ k, IsTag (N k) (unif a b (N k)) (unif a b (N k)) := by
    intro k i hi
    exact ⟨le_rfl, (unif_isPart hab (hNpos k)).step i hi⟩
  have hmeshle : ∀ k j, j ≤ k → ∀ i < N k, unif a b (N k) (i + 1) - unif a b (N k) i ≤ d j := by
    intro k j hjk i _
    exact le_trans (unif_mesh hab (hNpos k) i)
      (le_trans (le_of_lt (hNmesh k)) (hDle k j hjk))
  -- the sequence of uniform sums is Cauchy
  have hclose : ∀ k l, k ≤ l → |S k - S l| ≤ 1 / ((k : ℝ) + 1) := by
    intro k l hkl
    have h1 : ∀ i < N k, unif a b (N k) (i + 1) - unif a b (N k) i ≤ d k :=
      hmeshle k k le_rfl
    have h2 : ∀ i < N l, unif a b (N l) (i + 1) - unif a b (N l) i ≤ d k :=
      hmeshle l k hkl
    have := rs_compare (x := x) (v := v) hv (le_of_lt (hωpos k)) (hdspec k)
      (unif_isPart hab (hNpos k)) (hunifTag k) h1
      (unif_isPart hab (hNpos l)) (hunifTag l) h2
    simp only [hSdef]
    rw [← hV] at this
    exact le_trans this (hωbound k)
  have hcauchy : CauchySeq S := by
    refine cauchySeq_of_le_tendsto_0 (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) ?_ ?_
    · intro n m K hn hm
      rw [Real.dist_eq]
      have h1 := hclose K n hn
      have h2 := hclose K m hm
      have : |S n - S m| ≤ |S K - S n| + |S K - S m| := by
        calc |S n - S m| = |(S K - S m) - (S K - S n)| := by ring_nf
          _ ≤ |S K - S m| + |S K - S n| := abs_sub _ _
          _ = |S K - S n| + |S K - S m| := by ring
      linarith
    · have : Filter.Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.const_mul 2
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hSI : ∀ k, |S k - I| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hlim : Filter.Tendsto (fun l => |S k - S l|) Filter.atTop (nhds |S k - I|) :=
      (continuous_abs.tendsto _).comp ((tendsto_const_nhds).sub hI)
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop k] with l hl
    exact hclose k l hl
  refine ⟨I, ?_⟩
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * (1 / ((k : ℝ) + 1)) ≤ ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
    refine ⟨k, ?_⟩
    have hkpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hkpos]
    have : 2 / ε < (k : ℝ) := hk
    rw [div_lt_iff₀ hε] at this
    nlinarith
  refine ⟨D k, hDpos k, ?_⟩
  intro n t ξ h0 hn hmono hmesh htag
  have hpart : IsPart a b n t := ⟨h0, hn, hmono⟩
  have htag' : IsTag n t ξ := htag
  have hmeshd : ∀ i < n, t (i + 1) - t i ≤ d k := by
    intro i hi
    exact le_trans (le_of_lt (hmesh i hi)) (hDle k k le_rfl)
  have hcmp := rs_compare (x := x) (v := v) hv (le_of_lt (hωpos k)) (hdspec k)
    hpart htag' hmeshd
    (unif_isPart hab (hNpos k)) (hunifTag k) (hmeshle k k le_rfl)
  rw [← hV] at hcmp
  have h1 : |rsSum x v n t ξ - S k| ≤ 1 / ((k : ℝ) + 1) := by
    simp only [hSdef]; exact le_trans hcmp (hωbound k)
  have h2 := hSI k
  have h3 : |(∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))) - I|
      ≤ |rsSum x v n t ξ - S k| + |S k - I| := by
    have : (∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))) = rsSum x v n t ξ := rfl
    rw [this]
    calc |rsSum x v n t ξ - I| = |(rsSum x v n t ξ - S k) + (S k - I)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith


/-! ### Uniqueness, bounds and linearity -/

/-- A uniform partition of prescribed fineness exists. -/
theorem exists_fine {a b : ℝ} (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, unif a b k (i + 1) - unif a b k i < δ := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨k + 1, Nat.succ_pos k, fun i => ?_⟩
  have hkpos : (0:ℝ) < ((k : ℝ) + 1) := by positivity
  have h1 : (b - a) / ((k : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hkpos]
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  refine lt_of_le_of_lt ?_ h1
  have := unif_mesh hab (Nat.succ_pos k) (a := a) (b := b) i
  push_cast at this ⊢
  exact this

theorem rs_unique {x v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {I J : ℝ}
    (hI : VectorSpaceOpt_is_rs_integral x v a b I)
    (hJ : VectorSpaceOpt_is_rs_integral x v a b J) : I = J := by
  by_contra hne
  obtain ⟨ε, hεpos, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ 2 * ε < |I - J| := by
    refine ⟨|I - J| / 4, by positivity, ?_⟩
    have : 0 < |I - J| := abs_pos.2 (sub_ne_zero.2 hne)
    linarith
  obtain ⟨δ₁, hδ₁, h₁⟩ := hI ε hεpos
  obtain ⟨δ₂, hδ₂, h₂⟩ := hJ ε hεpos
  obtain ⟨k, hkpos, hkmesh⟩ := exists_fine hab (lt_min hδ₁ hδ₂)
  have hp := unif_isPart hab hkpos (a := a) (b := b)
  have hA := h₁ k (unif a b k) (unif a b k) hp.left hp.right hp.step
    (fun i _ => lt_of_lt_of_le (hkmesh i) (min_le_left _ _))
    (fun i hi => ⟨le_rfl, hp.step i hi⟩)
  have hB := h₂ k (unif a b k) (unif a b k) hp.left hp.right hp.step
    (fun i _ => lt_of_lt_of_le (hkmesh i) (min_le_right _ _))
    (fun i hi => ⟨le_rfl, hp.step i hi⟩)
  obtain ⟨Sk, hSk⟩ : ∃ z : ℝ,
      z = ∑ i ∈ Finset.range k,
        x (unif a b k i) * (v (unif a b k (i + 1)) - v (unif a b k i)) := ⟨_, rfl⟩
  have hIJ : |I - J| ≤ 2 * ε := by
    have h3 : |I - J| ≤ |Sk - I| + |Sk - J| := by
      calc |I - J| = |(Sk - J) - (Sk - I)| := by ring_nf
        _ ≤ |Sk - J| + |Sk - I| := abs_sub _ _
        _ = |Sk - I| + |Sk - J| := by ring
    rw [hSk] at h3
    linarith
  linarith

theorem rs_abs_le {x v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hv : BoundedVariationOn v (Set.Icc a b))
    {C : ℝ} (hC : 0 ≤ C) (hxC : ∀ p ∈ Set.Icc a b, |x p| ≤ C)
    {I : ℝ} (hI : VectorSpaceOpt_is_rs_integral x v a b I) :
    |I| ≤ C * VectorSpaceOpt_total_variation v a b := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨δ, hδ, hspec⟩ := hI ε hε
  obtain ⟨k, hkpos, hkmesh⟩ := exists_fine hab hδ
  have hp := unif_isPart hab hkpos (a := a) (b := b)
  have hA := hspec k (unif a b k) (unif a b k) hp.left hp.right hp.step
    (fun i _ => hkmesh i) (fun i hi => ⟨le_rfl, hp.step i hi⟩)
  have hSbound : |∑ i ∈ Finset.range k,
      x (unif a b k i) * (v (unif a b k (i + 1)) - v (unif a b k i))|
      ≤ C * VectorSpaceOpt_total_variation v a b := by
    calc |∑ i ∈ Finset.range k,
          x (unif a b k i) * (v (unif a b k (i + 1)) - v (unif a b k i))|
        ≤ ∑ i ∈ Finset.range k,
          |x (unif a b k i) * (v (unif a b k (i + 1)) - v (unif a b k i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range k, C * |v (unif a b k (i + 1)) - v (unif a b k i)| := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (hxC _ (hp.mem i (le_of_lt (Finset.mem_range.1 hi)))) (abs_nonneg _)
      _ = C * ∑ i ∈ Finset.range k, |v (unif a b k (i + 1)) - v (unif a b k i)| := by
          rw [Finset.mul_sum]
      _ ≤ C * VectorSpaceOpt_total_variation v a b :=
          mul_le_mul_of_nonneg_left (varsum_le hv hp.mono hp.mem) hC
  have hlast := abs_sub_abs_le_abs_sub I
    (∑ i ∈ Finset.range k, x (unif a b k i) * (v (unif a b k (i + 1)) - v (unif a b k i)))
  rw [abs_sub_comm] at hlast
  linarith [hA, hSbound, hlast]

theorem rs_add {x y v : ℝ → ℝ} {a b I J : ℝ}
    (hI : VectorSpaceOpt_is_rs_integral x v a b I)
    (hJ : VectorSpaceOpt_is_rs_integral y v a b J) :
    VectorSpaceOpt_is_rs_integral (fun s => x s + y s) v a b (I + J) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hI (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hJ (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro n t ξ h0 hn hmono hmesh htag
  have hA := h₁ n t ξ h0 hn hmono (fun i hi => lt_of_lt_of_le (hmesh i hi) (min_le_left _ _)) htag
  have hB := h₂ n t ξ h0 hn hmono (fun i hi => lt_of_lt_of_le (hmesh i hi) (min_le_right _ _)) htag
  have hsplit : (∑ i ∈ Finset.range n, (x (ξ i) + y (ξ i)) * (v (t (i + 1)) - v (t i)))
      = (∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i)))
        + ∑ i ∈ Finset.range n, y (ξ i) * (v (t (i + 1)) - v (t i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  calc |(∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i)))
          + (∑ i ∈ Finset.range n, y (ξ i) * (v (t (i + 1)) - v (t i))) - (I + J)|
      = |((∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))) - I)
          + ((∑ i ∈ Finset.range n, y (ξ i) * (v (t (i + 1)) - v (t i))) - J)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε := by linarith

theorem rs_smul {x v : ℝ → ℝ} {a b I : ℝ} (c : ℝ)
    (hI : VectorSpaceOpt_is_rs_integral x v a b I) :
    VectorSpaceOpt_is_rs_integral (fun s => c * x s) v a b (c * I) := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨1, one_pos, ?_⟩
    intro n t ξ _ _ _ _ _
    simp only [zero_mul, Finset.sum_const_zero, sub_zero, abs_zero]
    linarith
  · have hcpos : 0 < |c| := abs_pos.2 hc
    obtain ⟨δ, hδ, h⟩ := hI (ε / |c|) (by positivity)
    refine ⟨δ, hδ, ?_⟩
    intro n t ξ h0 hn hmono hmesh htag
    have hA := h n t ξ h0 hn hmono hmesh htag
    have hsplit : (∑ i ∈ Finset.range n, c * x (ξ i) * (v (t (i + 1)) - v (t i)))
        = c * ∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, ← mul_sub, abs_mul]
    calc |c| * |(∑ i ∈ Finset.range n, x (ξ i) * (v (t (i + 1)) - v (t i))) - I|
        ≤ |c| * (ε / |c|) := mul_le_mul_of_nonneg_left hA (le_of_lt hcpos)
      _ = ε := by field_simp


/-! ### The functional attached to a function of bounded variation -/

/-- Uniform continuity of a continuous function on `[a,b]`, extended to `ℝ`. -/
theorem IccExtend_uc {a b : ℝ} (hab : a ≤ b) (X : C(Set.Icc a b, ℝ)) :
    ∀ ε > 0, ∃ δ > 0, ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b,
      |p - q| ≤ δ → |Set.IccExtend hab X p - Set.IccExtend hab X q| ≤ ε := by
  have hcont : Continuous (Set.IccExtend hab X) := X.continuous.Icc_extend'
  have huc : UniformContinuousOn (Set.IccExtend hab X) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff_le.1 huc ε hε
  refine ⟨δ, hδ, fun p hp q hq hpq => ?_⟩
  have h2 := h p hp q hq (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at h2

open Classical in
/-- The Riemann–Stieltjes integral as a function, `0` when it fails to exist. -/
noncomputable def rsInt (x v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if h : ∃ I, VectorSpaceOpt_is_rs_integral x v a b I then h.choose else 0

theorem rsInt_spec {x v : ℝ → ℝ} {a b : ℝ}
    (h : ∃ I, VectorSpaceOpt_is_rs_integral x v a b I) :
    VectorSpaceOpt_is_rs_integral x v a b (rsInt x v a b) := by
  rw [rsInt, dif_pos h]
  exact h.choose_spec

theorem rsInt_eq {x v : ℝ → ℝ} {a b I : ℝ} (hab : a ≤ b)
    (hI : VectorSpaceOpt_is_rs_integral x v a b I) : rsInt x v a b = I :=
  rs_unique hab (rsInt_spec ⟨I, hI⟩) hI

/-- Every function of bounded variation defines a bounded functional on `C[a,b]`. -/
theorem riesz_converse (a b : ℝ) (hab : a ≤ b) (v : ℝ → ℝ)
    (hv : BoundedVariationOn v (Set.Icc a b)) :
    ∃ f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ,
      (∀ X : C(Set.Icc a b, ℝ),
        VectorSpaceOpt_is_rs_integral (Set.IccExtend hab X) v a b (f X)) ∧
      ‖f‖ ≤ VectorSpaceOpt_total_variation v a b := by
  have hTV : 0 ≤ VectorSpaceOpt_total_variation v a b := by
    rw [VectorSpaceOpt_total_variation]; exact ENNReal.toReal_nonneg
  have hex : ∀ X : C(Set.Icc a b, ℝ),
      ∃ I, VectorSpaceOpt_is_rs_integral (Set.IccExtend hab X) v a b I :=
    fun X => rs_exists hab hv (IccExtend_uc hab X)
  set L : C(Set.Icc a b, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun X => rsInt (Set.IccExtend hab X) v a b
      map_add' := by
        intro X Y
        have h3 := rs_add (rsInt_spec (hex X)) (rsInt_spec (hex Y))
        have heq : (fun s => Set.IccExtend hab X s + Set.IccExtend hab Y s)
            = Set.IccExtend hab (X + Y) := by
          funext s; simp [Set.IccExtend]
        rw [heq] at h3
        exact rsInt_eq hab h3
      map_smul' := by
        intro c X
        have h3 := rs_smul c (rsInt_spec (hex X))
        have heq : (fun s => c * Set.IccExtend hab X s) = Set.IccExtend hab (c • X) := by
          funext s; simp [Set.IccExtend]
        rw [heq] at h3
        simpa using rsInt_eq hab h3 } with hLdef
  have hbd : ∀ X : C(Set.Icc a b, ℝ),
      ‖L X‖ ≤ VectorSpaceOpt_total_variation v a b * ‖X‖ := by
    intro X
    have hxC : ∀ p ∈ Set.Icc a b, |Set.IccExtend hab X p| ≤ ‖X‖ := by
      intro p _
      have h2 := X.norm_coe_le_norm (Set.projIcc a b hab p)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have hkey := rs_abs_le hab hv (norm_nonneg X) hxC (rsInt_spec (hex X))
    rw [Real.norm_eq_abs]
    calc |L X| ≤ ‖X‖ * VectorSpaceOpt_total_variation v a b := hkey
      _ = VectorSpaceOpt_total_variation v a b * ‖X‖ := by ring
  refine ⟨L.mkContinuous _ hbd, fun X => rsInt_spec (hex X), ?_⟩
  exact L.mkContinuous_norm_le hTV hbd

end RS


open Set Filter Topology

namespace RS

/-! ### Bounded functions on `[a,b]` and the Hahn–Banach extension -/

/-- The space of all bounded real functions on `[a,b]`, with the supremum norm. -/
abbrev BF (a b : ℝ) := lp (fun _ : Set.Icc a b => ℝ) ⊤

variable {a b : ℝ}

/-- A continuous function on `[a,b]`, viewed as a bounded function. -/
noncomputable def emb (X : C(Set.Icc a b, ℝ)) : BF a b :=
  ⟨fun i => X i, memℓp_infty ⟨‖X‖, by rintro _ ⟨i, rfl⟩; exact X.norm_coe_le_norm i⟩⟩

@[simp] theorem emb_apply (X : C(Set.Icc a b, ℝ)) (i : Set.Icc a b) : emb X i = X i := rfl

theorem emb_norm (X : C(Set.Icc a b, ℝ)) : ‖(emb X : BF a b)‖ = ‖X‖ := by
  rw [lp.norm_eq_ciSup, ContinuousMap.norm_eq_iSup_norm]
  rfl

/-- The embedding as a linear map. -/
noncomputable def embL : C(Set.Icc a b, ℝ) →ₗ[ℝ] BF a b where
  toFun := emb
  map_add' := by
    intro X Y
    apply lp.ext
    funext i
    simp only [emb, lp.coeFn_add, Pi.add_apply, ContinuousMap.add_apply]
  map_smul' := by
    intro c X
    apply lp.ext
    funext i
    simp only [emb, lp.coeFn_smul, Pi.smul_apply, ContinuousMap.smul_apply, RingHom.id_apply,
      smul_eq_mul]

@[simp] theorem embL_apply (X : C(Set.Icc a b, ℝ)) : embL X = (emb X : BF a b) := rfl

theorem embL_injective : Function.Injective (embL (a := a) (b := b)) := by
  intro X Y h
  have h1 : ‖X - Y‖ = 0 := by
    rw [← emb_norm, ← embL_apply, map_sub, h, sub_self, norm_zero]
  have h2 : X - Y = 0 := by rwa [norm_eq_zero] at h1
  exact sub_eq_zero.1 h2


/-- Hahn–Banach: a bounded functional on `C[a,b]` extends to all bounded functions,
with no increase of norm. -/
theorem exists_extension (f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) :
    ∃ F : BF a b →L[ℝ] ℝ, (∀ X : C(Set.Icc a b, ℝ), F (embL X) = f X) ∧ ‖F‖ ≤ ‖f‖ := by
  obtain ⟨E, hE⟩ : ∃ E, E = LinearEquiv.ofInjective (embL (a := a) (b := b)) embL_injective :=
    ⟨_, rfl⟩
  have hEcoe : ∀ X : C(Set.Icc a b, ℝ), ((E X : LinearMap.range (embL (a := a) (b := b))) : BF a b)
      = embL X := by
    intro X; rw [hE]; exact LinearEquiv.ofInjective_apply _ _
  obtain ⟨g, hg⟩ : ∃ g : (LinearMap.range (embL (a := a) (b := b))) →ₗ[ℝ] ℝ,
      g = f.toLinearMap.comp E.symm.toLinearMap := ⟨_, rfl⟩
  have hgb : ∀ y : (LinearMap.range (embL (a := a) (b := b))), ‖g y‖ ≤ ‖f‖ * ‖y‖ := by
    intro y
    have hy : ((E (E.symm y) : LinearMap.range (embL (a := a) (b := b))) : BF a b) = (y : BF a b) := by
      rw [LinearEquiv.apply_symm_apply]
    have hy2 : (y : BF a b) = embL (E.symm y) := by rw [← hy, hEcoe]
    have hgy : g y = f (E.symm y) := by rw [hg]; rfl
    rw [hgy]
    calc ‖f (E.symm y)‖ ≤ ‖f‖ * ‖E.symm y‖ := f.le_opNorm _
      _ = ‖f‖ * ‖(y : BF a b)‖ := by rw [hy2, embL_apply, emb_norm]
      _ = ‖f‖ * ‖y‖ := rfl
  obtain ⟨F, hFeq, hFnorm⟩ :=
    Real.exists_extension_norm_eq (LinearMap.range (embL (a := a) (b := b)))
      (LinearMap.mkContinuous g ‖f‖ hgb)
  refine ⟨F, ?_, ?_⟩
  · intro X
    have h1 := hFeq (E X)
    rw [hEcoe X] at h1
    rw [h1]
    simp only [LinearMap.mkContinuous_apply, hg, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe]
  · rw [hFnorm]
    exact LinearMap.mkContinuous_norm_le g (norm_nonneg f) hgb

/-! ### Indicators -/

/-- The indicator of a subset of `ℝ`, restricted to `[a,b]`, as a bounded function. -/
noncomputable def ind (S : Set ℝ) : BF a b :=
  ⟨fun i => Set.indicator S (fun _ => (1:ℝ)) (i : ℝ),
   memℓp_infty ⟨1, by
     rintro _ ⟨i, rfl⟩
     exact le_trans (_root_.norm_indicator_le_norm_self (fun _ => (1:ℝ)) (i : ℝ)) (by norm_num)⟩⟩

@[simp] theorem ind_apply (S : Set ℝ) (i : Set.Icc a b) :
    (ind S : BF a b) i = Set.indicator S (fun _ => (1:ℝ)) (i : ℝ) := rfl

theorem ind_mem {S : Set ℝ} {i : Set.Icc a b} (h : (i : ℝ) ∈ S) : (ind S : BF a b) i = 1 := by
  rw [ind_apply, Set.indicator_of_mem h]

theorem ind_notMem {S : Set ℝ} {i : Set.Icc a b} (h : (i : ℝ) ∉ S) :
    (ind S : BF a b) i = 0 := by
  rw [ind_apply, Set.indicator_of_notMem h]

theorem ind_sub {S T : Set ℝ} (h : S ⊆ T) : (ind T : BF a b) - ind S = ind (T \ S) := by
  apply lp.ext
  funext i
  simp only [lp.coeFn_sub, Pi.sub_apply]
  by_cases h1 : (i : ℝ) ∈ S
  · rw [ind_mem h1, ind_mem (h h1), ind_notMem (by simp [h1])]; ring
  · by_cases h2 : (i : ℝ) ∈ T
    · rw [ind_notMem h1, ind_mem h2, ind_mem (Set.mem_diff_of_mem h2 h1)]; ring
    · rw [ind_notMem h1, ind_notMem h2, ind_notMem (by simp [h2])]; ring



/-- A sum of scaled indicators of pairwise disjoint sets has norm at most the bound on
the coefficients. -/
theorem norm_sum_ind_le {N : ℕ} (D : ℕ → Set ℝ) (c : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hdisj : ∀ i, i < N → ∀ j, j < N → i ≠ j → ∀ z : ℝ, z ∈ D i → z ∉ D j)
    (hc : ∀ i, i < N → |c i| ≤ M) :
    ‖(∑ i ∈ Finset.range N, c i • (ind (D i) : BF a b))‖ ≤ M := by
  refine lp.norm_le_of_forall_le hM ?_
  intro j
  have hval : (∑ i ∈ Finset.range N, c i • (ind (D i) : BF a b)) j
      = ∑ i ∈ Finset.range N, c i * Set.indicator (D i) (fun _ => (1:ℝ)) (j : ℝ) := by
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      ind_apply]
  rw [hval]
  by_cases hex : ∃ i, i < N ∧ (j : ℝ) ∈ D i
  · obtain ⟨i₀, hi₀N, hi₀⟩ := hex
    have hsum : (∑ i ∈ Finset.range N, c i * Set.indicator (D i) (fun _ => (1:ℝ)) (j : ℝ))
        = c i₀ := by
      rw [Finset.sum_eq_single i₀]
      · rw [Set.indicator_of_mem hi₀]; ring
      · intro i hi hne
        rw [Set.indicator_of_notMem (hdisj i₀ hi₀N i (Finset.mem_range.1 hi) (Ne.symm hne) _ hi₀)]
        ring
      · intro hcon
        exact absurd (Finset.mem_range.2 hi₀N) hcon
    rw [hsum, Real.norm_eq_abs]
    exact hc i₀ hi₀N
  · push_neg at hex
    have hsum : (∑ i ∈ Finset.range N, c i * Set.indicator (D i) (fun _ => (1:ℝ)) (j : ℝ))
        = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Set.indicator_of_notMem (hex i (Finset.mem_range.1 hi))]
      ring
    rw [hsum]
    simpa using hM

/-! ### The representing function -/

/-- The initial segment `[a, t]` of `[a, b]`, empty for `t ≤ a`. -/
def Sset (a b t : ℝ) : Set ℝ := if t ≤ a then ∅ else Set.Icc a (min t b)

theorem Sset_bot (a b : ℝ) : Sset a b a = ∅ := by simp [Sset]

theorem Sset_top {a b : ℝ} (hab : a < b) : Sset a b b = Set.Icc a b := by
  rw [Sset, if_neg (by linarith), min_self]

theorem Sset_subset (a b t : ℝ) : Sset a b t ⊆ Set.Icc a b := by
  rw [Sset]
  split
  · exact Set.empty_subset _
  · exact Set.Icc_subset_Icc le_rfl (min_le_right _ _)

theorem Sset_mono (a b : ℝ) {s t : ℝ} (h : s ≤ t) : Sset a b s ⊆ Sset a b t := by
  rw [Sset, Sset]
  split
  · exact Set.empty_subset _
  · rename_i hs
    rw [if_neg (by linarith [not_le.1 hs])]
    exact Set.Icc_subset_Icc le_rfl (min_le_min h le_rfl)

theorem mem_Sset_ge {a b t z : ℝ} (h : z ∈ Sset a b t) : a ≤ z ∧ z ≤ t := by
  rw [Sset] at h
  split at h
  · exact absurd h (Set.notMem_empty z)
  · exact ⟨h.1, le_trans h.2 (min_le_left _ _)⟩

theorem notMem_Sset {a b t z : ℝ} (hz : a ≤ z) (hzb : z ≤ b) (h : z ∉ Sset a b t) : t ≤ z := by
  rw [Sset] at h
  split at h
  · rename_i ht; linarith
  · rename_i ht
    by_contra hcon
    push_neg at hcon
    exact h ⟨hz, le_min (le_of_lt hcon) hzb⟩


/-- The cells cut out by a monotone sample are pairwise disjoint. -/
theorem cells_disjoint (a b : ℝ) {N : ℕ} {u : ℕ → ℝ}
    (hu : ∀ i j, i ≤ j → j ≤ N → u i ≤ u j) :
    ∀ i, i < N → ∀ j, j < N → i ≠ j → ∀ z : ℝ,
      z ∈ (Sset a b (u (i + 1)) \ Sset a b (u i)) →
        z ∉ (Sset a b (u (j + 1)) \ Sset a b (u j)) := by
  intro i hi j hj hne z hz hz2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hz2.2 (Sset_mono a b (hu (i + 1) j hlt (le_of_lt hj)) hz.1)
  · exact hz.2 (Sset_mono a b (hu (j + 1) i hlt (le_of_lt hi)) hz2.1)

/-- The Riemann–Stieltjes increments of `t ↦ F (ind (Sset a b t))` are values of `F`
on the cell indicators. -/
theorem v0_diff {a b : ℝ} (F : BF a b →L[ℝ] ℝ) {s t : ℝ} (h : s ≤ t) :
    F (ind (Sset a b t)) - F (ind (Sset a b s)) = F (ind (Sset a b t \ Sset a b s)) := by
  rw [← map_sub, ind_sub (Sset_mono a b h)]

/-- Every variation sum of `t ↦ F (ind (Sset a b t))` is bounded by `‖F‖`. -/
theorem v0_sum_le {a b : ℝ} (F : BF a b →L[ℝ] ℝ) (N : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i j, i ≤ j → j ≤ N → u i ≤ u j) :
    (∑ i ∈ Finset.range N,
      |F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i)))|) ≤ ‖F‖ := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun i =>
      if 0 ≤ F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i))) then (1:ℝ) else -1 :=
    ⟨_, rfl⟩
  have hcabs : ∀ i, |c i| ≤ 1 := by
    intro i; simp only [hcdef]; split <;> simp
  have habs : ∀ i, |F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i)))|
      = c i * (F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i)))) := by
    intro i
    simp only [hcdef]
    split
    · rename_i h; rw [abs_of_nonneg h]; ring
    · rename_i h; rw [abs_of_neg (by linarith [not_le.1 h])]; ring
  have hstep : ∀ i, i < N →
      c i * (F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i))))
        = F (c i • (ind (Sset a b (u (i + 1)) \ Sset a b (u i)) : BF a b)) := by
    intro i hi
    rw [map_smul, v0_diff F (hu i (i + 1) (Nat.le_succ i) hi)]
    simp
  have hsum : (∑ i ∈ Finset.range N,
      |F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i)))|)
      = F (∑ i ∈ Finset.range N,
          c i • (ind (Sset a b (u (i + 1)) \ Sset a b (u i)) : BF a b)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [habs i, hstep i (Finset.mem_range.1 hi)]
  rw [hsum]
  calc F (∑ i ∈ Finset.range N,
        c i • (ind (Sset a b (u (i + 1)) \ Sset a b (u i)) : BF a b))
      ≤ ‖F (∑ i ∈ Finset.range N,
          c i • (ind (Sset a b (u (i + 1)) \ Sset a b (u i)) : BF a b))‖ := le_abs_self _
    _ ≤ ‖F‖ * ‖(∑ i ∈ Finset.range N,
          c i • (ind (Sset a b (u (i + 1)) \ Sset a b (u i)) : BF a b))‖ := F.le_opNorm _
    _ ≤ ‖F‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_sum_ind_le _ c zero_le_one (cells_disjoint a b hu) (fun i _ => hcabs i))
          (norm_nonneg F)
    _ = ‖F‖ := by ring

theorem v0_evariation_le {a b : ℝ} (F : BF a b →L[ℝ] ℝ) :
    eVariationOn (fun t => F (ind (Sset a b t))) (Set.Icc a b) ≤ ENNReal.ofReal ‖F‖ := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨N, u, humono, huS⟩
  simp only
  have hedist : ∀ i : ℕ,
      edist (F (ind (Sset a b (u (i + 1))))) (F (ind (Sset a b (u i))))
        = ENNReal.ofReal |F (ind (Sset a b (u (i + 1)))) - F (ind (Sset a b (u i)))| := by
    intro i; rw [edist_dist, Real.dist_eq]
  rw [Finset.sum_congr rfl (fun i _ => hedist i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (v0_sum_le F N u (fun i j hij _ => humono hij))


theorem Sset_of_le {a b t : ℝ} (h : t ≤ a) : Sset a b t = ∅ := by rw [Sset, if_pos h]

theorem Sset_of_ge {a b t : ℝ} (hab : a < b) (h : b ≤ t) : Sset a b t = Set.Icc a b := by
  rw [Sset, if_neg (by linarith), min_eq_right h]

/-- The cells cut out by a monotone sequence straddling `[a,b]` cover `[a,b]`. -/
theorem cells_cover {a b : ℝ} (hab : a < b) {n : ℕ} {T : ℕ → ℝ}
    (hT0 : T 0 ≤ a) (hTn : b ≤ T n) {z : ℝ} (hz : z ∈ Set.Icc a b) :
    ∃ i, i < n ∧ z ∈ (Sset a b (T (i + 1)) \ Sset a b (T i)) := by
  classical
  have hex : ∃ i, z ∈ Sset a b (T i) := ⟨n, by rw [Sset_of_ge hab hTn]; exact hz⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = Nat.find hex := ⟨_, rfl⟩
  have hm : z ∈ Sset a b (T m) := by rw [hmdef]; exact Nat.find_spec hex
  have hmle : m ≤ n := by
    rw [hmdef]; exact Nat.find_le (by rw [Sset_of_ge hab hTn]; exact hz)
  have hmne : m ≠ 0 := by
    intro hc
    rw [hc, Sset_of_le hT0] at hm
    exact absurd hm (Set.notMem_empty z)
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨k, by omega, ?_, ?_⟩
  · rw [← hk]; exact hm
  · rw [hmdef] at hk
    intro hcon
    exact absurd hcon (Nat.find_min hex (by omega))

/-- The core estimate: a step function built from the cells of a monotone sequence is
uniformly close to `X`, so `F` of it is close to `f X`. -/
theorem F_step_close {a b : ℝ} (hab : a < b) (F : BF a b →L[ℝ] ℝ) (X : C(Set.Icc a b, ℝ))
    {ω : ℝ} (hωnn : 0 ≤ ω) {n : ℕ} {T c : ℕ → ℝ}
    (hmono : ∀ i j, i ≤ j → j ≤ n → T i ≤ T j)
    (hT0 : T 0 ≤ a) (hTn : b ≤ T n)
    (hval : ∀ i, i < n → ∀ z, z ∈ Sset a b (T (i + 1)) \ Sset a b (T i) →
        |c i - Set.IccExtend (le_of_lt hab) X z| ≤ ω) :
    |(∑ i ∈ Finset.range n,
        c i * (F (ind (Sset a b (T (i + 1)))) - F (ind (Sset a b (T i))))) - F (embL X)|
      ≤ ‖F‖ * ω := by
  obtain ⟨y, hydef⟩ : ∃ y : BF a b, y = ∑ i ∈ Finset.range n,
      c i • (ind (Sset a b (T (i + 1)) \ Sset a b (T i)) : BF a b) := ⟨_, rfl⟩
  have hSy : (∑ i ∈ Finset.range n,
      c i * (F (ind (Sset a b (T (i + 1)))) - F (ind (Sset a b (T i))))) = F y := by
    rw [hydef, map_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [map_smul, v0_diff F (hmono i (i + 1) (Nat.le_succ i) (Finset.mem_range.1 hi))]
    simp
  have hclose : ∀ j : Set.Icc a b, ‖(y - embL X) j‖ ≤ ω := by
    intro j
    obtain ⟨i₀, hi₀n, hi₀⟩ := cells_cover hab hT0 hTn j.2
    have hyj : y j = c i₀ := by
      rw [hydef]
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        ind_apply]
      rw [Finset.sum_eq_single i₀]
      · rw [Set.indicator_of_mem hi₀]; ring
      · intro i hi hne
        rw [Set.indicator_of_notMem
          (cells_disjoint a b hmono i₀ hi₀n i (Finset.mem_range.1 hi) (Ne.symm hne) _ hi₀)]
        ring
      · intro hcon; exact absurd (Finset.mem_range.2 hi₀n) hcon
    have hXj : Set.IccExtend (le_of_lt hab) X (j : ℝ) = X j := Set.IccExtend_val _ _ j
    have hsub : (y - embL X) j = c i₀ - Set.IccExtend (le_of_lt hab) X (j : ℝ) := by
      simp only [lp.coeFn_sub, Pi.sub_apply, hyj, embL_apply, emb_apply, hXj]
    rw [hsub, Real.norm_eq_abs]
    exact hval i₀ hi₀n (j : ℝ) hi₀
  have hnorm : ‖y - embL X‖ ≤ ω := lp.norm_le_of_forall_le hωnn hclose
  rw [hSy, ← map_sub]
  calc |F (y - embL X)| ≤ ‖F‖ * ‖y - embL X‖ := by
        rw [← Real.norm_eq_abs]; exact F.le_opNorm _
    _ ≤ ‖F‖ * ω := mul_le_mul_of_nonneg_left hnorm (norm_nonneg F)

end RS


open Set Filter Topology

namespace RS

variable {a b : ℝ}

theorem ind_empty : (ind ∅ : BF a b) = 0 := by
  apply lp.ext
  funext i
  simp only [ind, lp.coeFn_zero, Pi.zero_apply, Set.indicator_empty']

/-- Shifting to the right of `a`, used to right-continuize. -/
noncomputable def shift (a h t : ℝ) : ℝ := if t ≤ a then a else t + h

theorem shift_mono {a h : ℝ} (hh : 0 ≤ h) {s t : ℝ} (hst : s ≤ t) :
    shift a h s ≤ shift a h t := by
  simp only [shift]
  by_cases h1 : s ≤ a
  · rw [if_pos h1]
    by_cases h2 : t ≤ a
    · rw [if_pos h2]
    · rw [if_neg h2]; push_neg at h2; linarith
  · push_neg at h1
    have h2 : ¬ t ≤ a := by push_neg; linarith
    rw [if_neg (by push_neg; exact h1), if_neg h2]
    linarith

theorem shift_ge {a h t : ℝ} (hh : 0 ≤ h) (ht : a ≤ t) : t ≤ shift a h t := by
  simp only [shift]
  split
  · rename_i h1; linarith
  · linarith

theorem shift_le {a h t : ℝ} (hh : 0 ≤ h) (ht : a ≤ t) : shift a h t ≤ t + h := by
  simp only [shift]
  split
  · rename_i h1; linarith
  · exact le_rfl


/-! ### The representing function and its right-continuous normalization -/

/-- The unnormalized representing function `t ↦ F (χ_{[a,t]})`. -/
noncomputable def wF (F : BF a b →L[ℝ] ℝ) (t : ℝ) : ℝ := F (ind (Sset a b t))

theorem wF_at_a (F : BF a b →L[ℝ] ℝ) : wF F a = 0 := by
  rw [wF, Sset_bot, ind_empty, map_zero]

theorem wF_bv (F : BF a b →L[ℝ] ℝ) : BoundedVariationOn (wF F) Set.univ := by
  have h : eVariationOn (wF F) Set.univ ≤ ENNReal.ofReal ‖F‖ := by
    rw [eVariationOn]
    refine iSup_le ?_
    rintro ⟨N, u, humono, huS⟩
    simp only
    have hedist : ∀ i : ℕ, edist (wF F (u (i + 1))) (wF F (u i))
        = ENNReal.ofReal |wF F (u (i + 1)) - wF F (u i)| := by
      intro i; rw [edist_dist, Real.dist_eq]
    rw [Finset.sum_congr rfl (fun i _ => hedist i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (v0_sum_le F N u (fun i j hij _ => humono hij))
  exact ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top)

/-- The normalized representing function: `0` at and below `a`, the right limit above. -/
noncomputable def vF (F : BF a b →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  if t ≤ a then 0 else Function.rightLim (wF F) t

theorem vF_at_a (F : BF a b →L[ℝ] ℝ) : vF F a = 0 := by rw [vF, if_pos le_rfl]

/-- The shifted evaluations converge to the normalized function. -/
theorem vF_shift_tendsto (F : BF a b →L[ℝ] ℝ) (t : ℝ) :
    Tendsto (fun h : ℝ => wF F (shift a h t)) (𝓝[>] 0) (𝓝 (vF F t)) := by
  by_cases ht : t ≤ a
  · have hconst : ∀ h : ℝ, wF F (shift a h t) = 0 := by
      intro h; rw [shift, if_pos ht, wF_at_a]
    simp only [hconst, vF, if_pos ht]
    exact tendsto_const_nhds
  · push_neg at ht
    have heq : ∀ h : ℝ, wF F (shift a h t) = wF F (t + h) := by
      intro h; rw [shift, if_neg (by linarith)]
    simp only [heq, vF, if_neg (by linarith : ¬ t ≤ a)]
    have h1 : Tendsto (fun h : ℝ => t + h) (𝓝[>] (0:ℝ)) (𝓝[>] t) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun h : ℝ => t + h) := continuous_const.add continuous_id
        have hc := hcont.tendsto (0:ℝ)
        simp only [add_zero] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact lt_add_of_pos_right t hh
    exact ((wF_bv F).tendsto_rightLim t).comp h1

theorem vF_sum_le (F : BF a b →L[ℝ] ℝ) (N : ℕ) (u : ℕ → ℝ) (hu : Monotone u) :
    (∑ i ∈ Finset.range N, |vF F (u (i + 1)) - vF F (u i)|) ≤ ‖F‖ := by
  have hlim : Tendsto (fun h : ℝ =>
      ∑ i ∈ Finset.range N, |wF F (shift a h (u (i + 1))) - wF F (shift a h (u i))|)
      (𝓝[>] (0:ℝ)) (𝓝 (∑ i ∈ Finset.range N, |vF F (u (i + 1)) - vF F (u i)|)) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    exact ((vF_shift_tendsto F (u (i + 1))).sub (vF_shift_tendsto F (u i))).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact v0_sum_le F N (fun i => shift a h (u i))
    (fun i j hij _ => shift_mono (le_of_lt hh) (hu hij))

theorem vF_evariation_le (F : BF a b →L[ℝ] ℝ) :
    eVariationOn (vF F) Set.univ ≤ ENNReal.ofReal ‖F‖ := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨N, u, humono, huS⟩
  simp only
  have hedist : ∀ i : ℕ, edist (vF F (u (i + 1))) (vF F (u i))
      = ENNReal.ofReal |vF F (u (i + 1)) - vF F (u i)| := by
    intro i; rw [edist_dist, Real.dist_eq]
  rw [Finset.sum_congr rfl (fun i _ => hedist i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (vF_sum_le F N u humono)

theorem vF_bv (F : BF a b →L[ℝ] ℝ) : BoundedVariationOn (vF F) (Set.Icc a b) := by
  have h1 : eVariationOn (vF F) (Set.Icc a b) ≤ eVariationOn (vF F) Set.univ :=
    eVariationOn.mono _ (Set.subset_univ _)
  exact ne_of_lt (lt_of_le_of_lt (le_trans h1 (vF_evariation_le F)) ENNReal.ofReal_lt_top)

theorem vF_tv_le (F : BF a b →L[ℝ] ℝ) :
    VectorSpaceOpt_total_variation (vF F) a b ≤ ‖F‖ := by
  rw [VectorSpaceOpt_total_variation]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg F) ?_
  exact le_trans (eVariationOn.mono _ (Set.subset_univ _)) (vF_evariation_le F)

theorem vF_right_cont (F : BF a b →L[ℝ] ℝ) {t : ℝ} (ht : a < t) :
    ContinuousWithinAt (vF F) (Set.Ici t) t := by
  have h1 : ContinuousWithinAt (Function.rightLim (wF F)) (Set.Ici t) t :=
    (wF_bv F).continuousWithinAt_rightLim
  refine h1.congr ?_ ?_
  · intro s hs
    have hs' : t ≤ s := hs
    rw [vF, if_neg (by linarith : ¬ s ≤ a)]
  · rw [vF, if_neg (by linarith : ¬ t ≤ a)]


/-! ### The representation -/

theorem vF_represents (hab : a < b) (f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) (F : BF a b →L[ℝ] ℝ)
    (hF : ∀ Y : C(Set.Icc a b, ℝ), F (embL Y) = f Y) (X : C(Set.Icc a b, ℝ)) :
    VectorSpaceOpt_is_rs_integral (Set.IccExtend (le_of_lt hab) X) (vF F) a b (f X) := by
  intro ε hε
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = ε / (‖F‖ + 1) := ⟨_, rfl⟩
  have hωpos : 0 < ω := by rw [hωdef]; positivity
  obtain ⟨δ', hδ', hmod⟩ := IccExtend_uc (le_of_lt hab) X ω hωpos
  refine ⟨δ' / 2, by linarith, ?_⟩
  intro n t ξ h0 hn hmono htmesh htag
  have hpart : IsPart a b n t := ⟨h0, hn, hmono⟩
  have hbound : ∀ h : ℝ, 0 < h → h ≤ δ' / 2 →
      |(∑ i ∈ Finset.range n, Set.IccExtend (le_of_lt hab) X (ξ i) *
        (wF F (shift a h (t (i + 1))) - wF F (shift a h (t i)))) - f X| ≤ ‖F‖ * ω := by
    intro h hh hhle
    rw [← hF X]
    simp only [wF]
    refine F_step_close (T := fun i => shift a h (t i))
      (c := fun i => Set.IccExtend (le_of_lt hab) X (ξ i)) hab F X (le_of_lt hωpos)
      (fun i j hij hjn => shift_mono (le_of_lt hh) (hpart.mono i j hij hjn)) ?_ ?_ ?_
    · simp only []
      rw [h0, shift, if_pos le_rfl]
    · simp only []
      rw [hn]
      exact shift_ge (le_of_lt hh) (le_of_lt hab)
    · intro i hi z hz
      simp only [] at hz ⊢
      have hzmem : z ∈ Set.Icc a b := Sset_subset a b _ hz.1
      have hzhi : z ≤ shift a h (t (i + 1)) := (mem_Sset_ge hz.1).2
      have hzlo : shift a h (t i) ≤ z := notMem_Sset hzmem.1 hzmem.2 hz.2
      have hti : a ≤ t i := (hpart.mem i (le_of_lt hi)).1
      have hti1 : t (i + 1) ∈ Set.Icc a b := hpart.mem (i + 1) hi
      obtain ⟨hξ1, hξ2⟩ := htag i hi
      have h1 : t i ≤ z := le_trans (shift_ge (le_of_lt hh) hti) hzlo
      have h2 : z ≤ t (i + 1) + h :=
        le_trans hzhi (shift_le (le_of_lt hh) (le_trans hti (hpart.mono i (i + 1)
          (Nat.le_succ i) hi)))
      have hm := htmesh i hi
      refine hmod (ξ i) ⟨le_trans hti hξ1, le_trans hξ2 hti1.2⟩ z hzmem ?_
      rw [abs_le]
      constructor <;> linarith
  have hlim : Tendsto (fun h : ℝ =>
      |(∑ i ∈ Finset.range n, Set.IccExtend (le_of_lt hab) X (ξ i) *
        (wF F (shift a h (t (i + 1))) - wF F (shift a h (t i)))) - f X|)
      (𝓝[>] (0:ℝ))
      (𝓝 |(∑ i ∈ Finset.range n, Set.IccExtend (le_of_lt hab) X (ξ i) *
        (vF F (t (i + 1)) - vF F (t i))) - f X|) := by
    refine Filter.Tendsto.abs ((tendsto_finsetSum _ (fun i _ => ?_)).sub tendsto_const_nhds)
    exact Filter.Tendsto.const_mul _
      ((vF_shift_tendsto F (t (i + 1))).sub (vF_shift_tendsto F (t i)))
  have hfin : |(∑ i ∈ Finset.range n, Set.IccExtend (le_of_lt hab) X (ξ i) *
      (vF F (t (i + 1)) - vF F (t i))) - f X| ≤ ‖F‖ * ω := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < δ' / 2 by linarith)] with h hh
    exact hbound h hh.1 hh.2
  refine le_trans hfin ?_
  rw [hωdef, mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < ‖F‖ + 1)]
  nlinarith [norm_nonneg F, hε.le]

/-- **Riesz representation theorem for `C[a,b]`.** -/
theorem riesz_forward (hab : a < b) (f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) :
    ∃ v : ℝ → ℝ, VectorSpaceOpt_is_nbv_open a b v ∧
      (∀ X : C(Set.Icc a b, ℝ),
        VectorSpaceOpt_is_rs_integral (Set.IccExtend (le_of_lt hab) X) v a b (f X)) ∧
      ‖f‖ = VectorSpaceOpt_total_variation v a b := by
  obtain ⟨F, hF, hFnorm⟩ := exists_extension f
  have hTVnn : 0 ≤ VectorSpaceOpt_total_variation (vF F) a b := by
    rw [VectorSpaceOpt_total_variation]; exact ENNReal.toReal_nonneg
  refine ⟨vF F, ⟨vF_bv F, vF_at_a F, fun t ht => vF_right_cont F ht.1⟩,
    fun X => vF_represents hab f F hF X, ?_⟩
  refine le_antisymm ?_ (le_trans (vF_tv_le F) hFnorm)
  refine f.opNorm_le_bound hTVnn (fun X => ?_)
  have hxC : ∀ p ∈ Set.Icc a b, |Set.IccExtend (le_of_lt hab) X p| ≤ ‖X‖ := by
    intro p _
    have h2 := X.norm_coe_le_norm (Set.projIcc a b (le_of_lt hab) p)
    rw [Real.norm_eq_abs] at h2
    exact h2
  have hkey := rs_abs_le (le_of_lt hab) (vF_bv F) (norm_nonneg X) hxC
    (vF_represents hab f F hF X)
  rw [Real.norm_eq_abs]
  calc |f X| ≤ ‖X‖ * VectorSpaceOpt_total_variation (vF F) a b := hkey
    _ = VectorSpaceOpt_total_variation (vF F) a b * ‖X‖ := by ring

end RS


theorem solution (a b : ℝ) (hab : a < b)
    (f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) :
    ∃ v : ℝ → ℝ, VectorSpaceOpt_is_nbv_open a b v ∧
      (∀ x : C(Set.Icc a b, ℝ),
        VectorSpaceOpt_is_rs_integral (Set.IccExtend (le_of_lt hab) x) v a b (f x)) ∧
      ‖f‖ = VectorSpaceOpt_total_variation v a b := by
  exact RS.riesz_forward hab f
