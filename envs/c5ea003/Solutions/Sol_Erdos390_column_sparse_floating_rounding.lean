-- Prove2me | solution 1 for Erdos390.column_sparse_floating_rounding
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T13:38:25.439542+00:00
-- url     : https://prove2.me/submissions/a14b8900-b401-4c78-8c46-4540f497e814

import Definitions.Def_erdos390_floating_rounding

/- Adapted from Shouqiao Wang, erdos, commit 61325b10bbdc29f4fb5e0618b414b9f2189333ad,
390/lean/Erdos390/WholePaper/FloatingRounding{Step,Counts,Rows,Discrepancy,}.lean. -/


/-!
# One rank-deficient floating-rounding step

This file isolates the linear-algebra move used in the paper's floating
rounding lemma.  If fewer equations than fractional coordinates are being
retained, one may preserve every retained equation, keep all coordinates in
`[0,1]`, freeze every already integral coordinate, and make at least one new
coordinate integral.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Coordinates strictly between the two integral boundary values. -/
def fractionalSupport {A : Type*} [Fintype A] (x : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ x a ≠ 0 ∧ x a ≠ 1

@[simp]
theorem mem_fractionalSupport {A : Type*} [Fintype A]
    {x : A → ℝ} {a : A} :
    a ∈ fractionalSupport x ↔ x a ≠ 0 ∧ x a ≠ 1 := by
  classical
  simp [fractionalSupport]

private theorem exists_positive_boundary_step
    {A : Type*} [Fintype A]
    (x z : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hstrict : ∀ a, z a ≠ 0 → 0 < x a ∧ x a < 1)
    (hz : z ≠ 0) :
    ∃ t : ℝ,
      0 < t ∧
      (∀ a, 0 ≤ x a + t * z a ∧ x a + t * z a ≤ 1) ∧
      ∃ a, z a ≠ 0 ∧
        (x a + t * z a = 0 ∨ x a + t * z a = 1) := by
  classical
  have hzexists : ∃ a, z a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  obtain ⟨a₁, ha₁⟩ := hzexists
  letI : Nonempty A := ⟨a₁⟩
  let ratio : A → ℝ := fun a ↦
    if 0 < z a then z a / (1 - x a)
    else if z a < 0 then (-z a) / x a
    else 0
  have hratio_nonneg (a : A) : 0 ≤ ratio a := by
    by_cases hp : 0 < z a
    · have hden : 0 < 1 - x a := sub_pos.mpr (hstrict a hp.ne').2
      simp only [ratio, if_pos hp]
      exact (div_pos hp hden).le
    · by_cases hn : z a < 0
      · have hden : 0 < x a := (hstrict a hn.ne).1
        simp only [ratio, if_neg hp, if_pos hn]
        exact (div_pos (neg_pos.mpr hn) hden).le
      · simp [ratio, hp, hn]
  have hratio_pos : 0 < ratio a₁ := by
    rcases lt_or_gt_of_ne ha₁ with hn | hp
    · have hxpos : 0 < x a₁ := (hstrict a₁ ha₁).1
      simp only [ratio, if_neg (not_lt.mpr hn.le), if_pos hn]
      exact div_pos (neg_pos.mpr hn) hxpos
    · have hxlt : x a₁ < 1 := (hstrict a₁ ha₁).2
      simp only [ratio, if_pos hp]
      exact div_pos hp (sub_pos.mpr hxlt)
  let K : ℝ := Finset.univ.sup' Finset.univ_nonempty ratio
  have hratio_le (a : A) : ratio a ≤ K := by
    exact Finset.le_sup' ratio (Finset.mem_univ a)
  have hKpos : 0 < K := hratio_pos.trans_le (hratio_le a₁)
  obtain ⟨a₀, -, hKmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty ratio
  refine ⟨K⁻¹, inv_pos.mpr hKpos, ?_, ?_⟩
  · intro a
    by_cases hp : 0 < z a
    · have hden : 0 < 1 - x a := sub_pos.mpr (hstrict a hp.ne').2
      have hr : z a / (1 - x a) ≤ K := by
        simpa only [ratio, if_pos hp] using hratio_le a
      have hzle : z a / K ≤ 1 - x a := by
        apply (div_le_iff₀ hKpos).2
        have := (div_le_iff₀ hden).1 hr
        simpa only [mul_comm] using this
      have hstep : K⁻¹ * z a = z a / K := by
        simp [div_eq_mul_inv, mul_comm]
      rw [hstep]
      have hzdiv : 0 ≤ z a / K := div_nonneg hp.le hKpos.le
      exact ⟨add_nonneg (hx a).1 hzdiv, by linarith⟩
    · by_cases hn : z a < 0
      · have hden : 0 < x a := (hstrict a hn.ne).1
        have hr : (-z a) / x a ≤ K := by
          simpa only [ratio, if_neg hp, if_pos hn] using hratio_le a
        have hzle : (-z a) / K ≤ x a := by
          apply (div_le_iff₀ hKpos).2
          have := (div_le_iff₀ hden).1 hr
          simpa only [mul_comm] using this
        have hstep : K⁻¹ * z a = z a / K := by
          simp [div_eq_mul_inv, mul_comm]
        rw [hstep]
        have hzneg : z a / K = -((-z a) / K) := by ring
        rw [hzneg]
        have hzdiv : 0 ≤ (-z a) / K :=
          div_nonneg (neg_nonneg.mpr hn.le) hKpos.le
        constructor <;> nlinarith [hx a]
      · have hz0 : z a = 0 := le_antisymm (not_lt.mp hp) (not_lt.mp hn)
        simp [hz0, hx a]
  · have hratio_a₀_pos : 0 < ratio a₀ := by
      rw [← hKmax]
      exact hKpos
    have hza₀ : z a₀ ≠ 0 := by
      intro hz0
      simp [ratio, hz0] at hratio_a₀_pos
    rcases lt_or_gt_of_ne hza₀ with hn | hp
    · have hxpos : 0 < x a₀ := (hstrict a₀ hza₀).1
      have hratio_eq : K = (-z a₀) / x a₀ := by
        simpa only [ratio, if_neg (not_lt.mpr hn.le), if_pos hn] using hKmax
      have hnum : -z a₀ = K * x a₀ :=
        (div_eq_iff hxpos.ne').1 hratio_eq.symm
      have hstep : K⁻¹ * z a₀ = -x a₀ := by
        calc
          K⁻¹ * z a₀ = z a₀ / K := by
            simp [div_eq_mul_inv, mul_comm]
          _ = -x a₀ := by
            apply (div_eq_iff hKpos.ne').2
            nlinarith [hnum]
      exact ⟨a₀, hza₀, Or.inl (by rw [hstep]; ring)⟩
    · have hxlt : x a₀ < 1 := (hstrict a₀ hza₀).2
      have hratio_eq : K = z a₀ / (1 - x a₀) := by
        simpa only [ratio, if_pos hp] using hKmax
      have hnum : z a₀ = K * (1 - x a₀) :=
        (div_eq_iff (sub_pos.mpr hxlt).ne').1 hratio_eq.symm
      have hstep : K⁻¹ * z a₀ = 1 - x a₀ := by
        calc
          K⁻¹ * z a₀ = z a₀ / K := by
            simp [div_eq_mul_inv, mul_comm]
          _ = 1 - x a₀ := by
            apply (div_eq_iff hKpos.ne').2
            nlinarith [hnum]
      exact ⟨a₀, hza₀, Or.inr (by rw [hstep]; ring)⟩

/-- A rank-deficient retained system admits a feasible move that freezes at
least one additional coordinate.  The weights are completely arbitrary;
the zero-one and sparsity hypotheses enter only in the later iteration. -/
theorem exists_floating_step
    {A E : Type*} [Fintype A] [Fintype E]
    (w : E → A → ℝ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hcard : Fintype.card E < (fractionalSupport x).card) :
    ∃ x' : A → ℝ,
      (∀ a, 0 ≤ x' a ∧ x' a ≤ 1) ∧
      (∀ a, x a = 0 ∨ x a = 1 → x' a = x a) ∧
      (∀ e, ∑ a, w e a * x' a = ∑ a, w e a * x a) ∧
      (fractionalSupport x').card < (fractionalSupport x).card := by
  classical
  let F : Finset A := fractionalSupport x
  let outside : Finset A := Finset.univ \ F
  let I : Type _ := ↥outside
  let L : (A → ℝ) →ₗ[ℝ] (Sum E I → ℝ) :=
    { toFun := fun z i ↦ match i with
        | Sum.inl e => ∑ a, w e a * z a
        | Sum.inr a => z a.1
      map_add' := by
        intro z z'
        funext i
        cases i with
        | inl e => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        | inr a => simp
      map_smul' := by
        intro c z
        funext i
        cases i with
        | inl e =>
            simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            change w e a * (c * z a) = c * (w e a * z a)
            ring
        | inr a => simp }
  have houtside : outside.card + F.card = Fintype.card A := by
    simpa only [outside, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
  have hdimNat : Fintype.card E + Fintype.card I < Fintype.card A := by
    have hIcard : Fintype.card I = outside.card := Fintype.card_coe outside
    have hcard' : Fintype.card E < F.card := by
      simpa only [F] using hcard
    rw [hIcard]
    omega
  have hdim :
      Module.finrank ℝ (Sum E I → ℝ) < Module.finrank ℝ (A → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using hdimNat
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨z, hzker, hzne⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hLzero : L z = 0 := hzker
  have hzoutside (a : A) (ha : a ∉ F) : z a = 0 := by
    have hai : a ∈ outside := by simp [outside, ha]
    have h := congrFun hLzero (Sum.inr (⟨a, hai⟩ : I))
    simpa only [L, Pi.zero_apply] using h
  have hzstrict (a : A) (hza : z a ≠ 0) : 0 < x a ∧ x a < 1 := by
    have haF : a ∈ F := by
      by_contra ha
      exact hza (hzoutside a ha)
    have hmem : x a ≠ 0 ∧ x a ≠ 1 := by
      simpa only [F, mem_fractionalSupport] using haF
    exact ⟨lt_of_le_of_ne (hx a).1 hmem.1.symm,
      lt_of_le_of_ne (hx a).2 hmem.2⟩
  obtain ⟨t, ht, hbounds, a₀, hza₀, ha₀⟩ :=
    exists_positive_boundary_step x z hx hzstrict hzne
  let x' : A → ℝ := fun a ↦ x a + t * z a
  refine ⟨x', ?_, ?_, ?_, ?_⟩
  · exact hbounds
  · intro a ha
    have haF : a ∉ F := by
      intro hmem
      have hfrac : x a ≠ 0 ∧ x a ≠ 1 := by
        simpa only [F, mem_fractionalSupport] using hmem
      exact ha.elim hfrac.1 hfrac.2
    simp [x', hzoutside a haF]
  · intro e
    have heq := congrFun hLzero (Sum.inl e)
    have hsumz : ∑ a, w e a * z a = 0 := by
      simpa only [L, Pi.zero_apply] using heq
    simp only [x', mul_add, Finset.sum_add_distrib]
    have hweighted : ∑ a, w e a * (t * z a) =
        t * ∑ a, w e a * z a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hweighted, hsumz, mul_zero, add_zero]
  · have hsub : fractionalSupport x' ⊆ fractionalSupport x := by
      intro a ha
      by_contra haF
      have hz0 : z a = 0 := hzoutside a (by simpa only [F] using haF)
      have hxa : x' a = x a := by simp [x', hz0]
      have hnot : a ∉ fractionalSupport x := by simpa only [F] using haF
      have hfrac := mem_fractionalSupport.mp ha
      exact hnot (mem_fractionalSupport.mpr (by simpa only [hxa] using hfrac))
    have ha₀F : a₀ ∈ fractionalSupport x := by
      by_contra hnot
      exact hza₀ (hzoutside a₀ (by simpa only [F] using hnot))
    have ha₀not : a₀ ∉ fractionalSupport x' := by
      rw [mem_fractionalSupport]
      exact fun h ↦ ha₀.elim h.1 h.2
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq ↦ ha₀not (heq ▸ ha₀F)⟩)

end

end Erdos390.WholePaper


/-!
# Counting retained equations in floating rounding

The paper retains active row equations and columns meeting more than `4*d`
currently fractional coordinates.  These elementary double-counts show that
their total number is strictly smaller than the number of fractional
coordinates, which is the hypothesis of `exists_floating_step`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def activeRows {A R : Type*} [Fintype A] [Fintype R]
    (F : Finset A) (row : A → R) : Finset R := by
  classical
  exact F.image row

def rowFiber {A R : Type*} [Fintype A]
    (F : Finset A) (row : A → R) (r : R) : Finset A := by
  classical
  exact F.filter fun a ↦ row a = r

def columnSupportIn {A C : Type*} [Fintype A]
    (F : Finset A) (inc : C → A → Prop) (c : C) : Finset A := by
  classical
  exact F.filter fun a ↦ inc c a


def heavyColumns {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (inc : C → A → Prop) (d : ℕ) : Finset C := by
  classical
  exact Finset.univ.filter fun c ↦
    4 * d < (columnSupportIn F inc c).card

@[simp]
theorem mem_activeRows {A R : Type*} [Fintype A] [Fintype R]
    {F : Finset A} {row : A → R} {r : R} :
    r ∈ activeRows F row ↔ ∃ a ∈ F, row a = r := by
  classical
  simp [activeRows]

@[simp]
theorem mem_rowFiber {A R : Type*} [Fintype A]
    {F : Finset A} {row : A → R} {r : R} {a : A} :
    a ∈ rowFiber F row r ↔ a ∈ F ∧ row a = r := by
  classical
  simp [rowFiber]

@[simp]
theorem mem_columnSupportIn {A C : Type*} [Fintype A]
    {F : Finset A} {inc : C → A → Prop} {c : C} {a : A} :
    a ∈ columnSupportIn F inc c ↔ a ∈ F ∧ inc c a := by
  classical
  simp [columnSupportIn]

@[simp]
theorem mem_columnsContaining {A C : Type*} [Fintype C]
    {H : Finset C} {inc : C → A → Prop} {a : A} {c : C} :
    c ∈ columnsContaining H inc a ↔ c ∈ H ∧ inc c a := by
  classical
  simp [columnsContaining]

@[simp]
theorem mem_heavyColumns {A C : Type*} [Fintype A] [Fintype C]
    {F : Finset A} {inc : C → A → Prop} {d : ℕ} {c : C} :
    c ∈ heavyColumns F inc d ↔
      4 * d < (columnSupportIn F inc c).card := by
  classical
  simp [heavyColumns]

/-- If every active row contains at least two fractional coordinates, active
rows consume at most half of the fractional-coordinate count. -/
theorem two_mul_card_activeRows_le
    {A R : Type*} [Fintype A] [Fintype R]
    (F : Finset A) (row : A → R)
    (htwo : ∀ r ∈ activeRows F row,
      2 ≤ (rowFiber F row r).card) :
    2 * (activeRows F row).card ≤ F.card := by
  classical
  have hmaps : (F : Set A).MapsTo row (activeRows F row) := by
    intro a ha
    exact mem_activeRows.mpr ⟨a, ha, rfl⟩
  have hpartition :
      F.card = ∑ r ∈ activeRows F row, (rowFiber F row r).card := by
    simpa only [rowFiber] using
      (Finset.card_eq_sum_card_fiberwise hmaps)
  rw [hpartition]
  calc
    2 * (activeRows F row).card =
        ∑ _r ∈ activeRows F row, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ activeRows F row, (rowFiber F row r).card := by
      exact Finset.sum_le_sum fun r hr ↦ htwo r hr

private theorem incidence_sum_swap
    {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (H : Finset C) (inc : C → A → Prop) :
    (∑ c ∈ H, (columnSupportIn F inc c).card) =
      ∑ a ∈ F, (columnsContaining H inc a).card := by
  classical
  simp only [columnSupportIn, columnsContaining, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]

/-- With column degree at most `d`, fewer than one quarter of the fractional
coordinates can index columns that contain more than `4*d` of them. -/
theorem four_mul_card_heavyColumns_lt
    {A C : Type*} [Fintype A] [Fintype C]
    (F : Finset A) (inc : C → A → Prop) (d : ℕ)
    (hF : F.Nonempty)
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    4 * (heavyColumns F inc d).card < F.card := by
  classical
  let H : Finset C := heavyColumns F inc d
  let total : ℕ := ∑ c ∈ H, (columnSupportIn F inc c).card
  have hlower : (4 * d + 1) * H.card ≤ total := by
    calc
      (4 * d + 1) * H.card = ∑ _c ∈ H, (4 * d + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ H, (columnSupportIn F inc c).card := by
        apply Finset.sum_le_sum
        intro c hc
        have hc' : 4 * d < (columnSupportIn F inc c).card := by
          simpa only [H, mem_heavyColumns] using hc
        omega
      _ = total := rfl
  have hupper : total ≤ d * F.card := by
    dsimp only [total]
    rw [incidence_sum_swap F H inc]
    calc
      (∑ a ∈ F, (columnsContaining H inc a).card) ≤
          ∑ _a ∈ F, d := by
        apply Finset.sum_le_sum
        intro a _
        exact (Finset.card_le_card (by
          intro c hc
          have hcInc : inc c a := (mem_columnsContaining.mp hc).2
          exact mem_columnsContaining.mpr ⟨Finset.mem_univ c, hcInc⟩)).trans
            (hsparse a)
      _ = d * F.card := by simp [Nat.mul_comm]
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  by_cases hd : d = 0
  · have hH : H.card = 0 := by
      subst d
      simp only [Nat.mul_zero, zero_add, one_mul] at hlower hupper
      omega
    simpa only [H, hH, mul_zero] using hFpos
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    by_cases hHzero : H.card = 0
    · simpa only [H, hHzero, mul_zero] using hFpos
    · have hHpos : 0 < H.card := Nat.pos_of_ne_zero hHzero
      by_contra hnot
      have hmle : F.card ≤ 4 * H.card := Nat.le_of_not_gt hnot
      have hpoly : (4 * d + 1) * H.card ≤ 4 * d * H.card := by
        calc
          (4 * d + 1) * H.card ≤ total := hlower
          _ ≤ d * F.card := hupper
          _ ≤ d * (4 * H.card) := Nat.mul_le_mul_left d hmle
          _ = 4 * d * H.card := by ring
      nlinarith

/-- The retained active-row and heavy-column equations together have rank
strictly below the number of fractional coordinates. -/
theorem card_activeRows_add_heavyColumns_lt
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (F : Finset A) (row : A → R) (inc : C → A → Prop) (d : ℕ)
    (hF : F.Nonempty)
    (htwo : ∀ r ∈ activeRows F row,
      2 ≤ (rowFiber F row r).card)
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    (activeRows F row).card + (heavyColumns F inc d).card < F.card := by
  have hrow := two_mul_card_activeRows_le F row htwo
  have hcol := four_mul_card_heavyColumns_lt F inc d hF hsparse
  omega

end

end Erdos390.WholePaper


/-!
# Integer row sums force two fractional coordinates

After integral coordinates are frozen, an active row cannot contain exactly
one fractional coordinate: the whole row sum is an integer and every other
entry is zero or one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section


@[simp]
theorem mem_rowSet {A R : Type*} [Fintype A]
    {row : A → R} {r : R} {a : A} :
    a ∈ rowSet row r ↔ row a = r := by
  classical
  simp [rowSet]

private theorem eq_zero_or_one_of_not_fractional
    {A : Type*} [Fintype A] {x : A → ℝ} {a : A}
    (ha : a ∉ fractionalSupport x) :
    x a = 0 ∨ x a = 1 := by
  by_contra h
  push_neg at h
  exact ha (mem_fractionalSupport.mpr h)

/-- The exact row-count fact used at every iteration of floating rounding. -/
theorem two_le_card_rowFiber_of_integer_rowSums
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ)) :
    ∀ r ∈ activeRows (fractionalSupport x) row,
      2 ≤ (rowFiber (fractionalSupport x) row r).card := by
  classical
  intro r hr
  have hfiberNe : (rowFiber (fractionalSupport x) row r).Nonempty := by
    obtain ⟨a, haF, har⟩ := mem_activeRows.mp hr
    exact ⟨a, mem_rowFiber.mpr ⟨haF, har⟩⟩
  by_contra hnot
  have hcardOne : (rowFiber (fractionalSupport x) row r).card = 1 := by
    have hpos : 0 < (rowFiber (fractionalSupport x) row r).card :=
      Finset.card_pos.mpr hfiberNe
    omega
  obtain ⟨a, haFiber⟩ := Finset.card_eq_one.mp hcardOne
  have haMem : a ∈ rowFiber (fractionalSupport x) row r := by
    rw [haFiber]
    simp
  have haFrac : a ∈ fractionalSupport x := (mem_rowFiber.mp haMem).1
  have harow : row a = r := (mem_rowFiber.mp haMem).2
  have haxpos : 0 < x a :=
    lt_of_le_of_ne (hx a).1 (mem_fractionalSupport.mp haFrac).1.symm
  have haxlt : x a < 1 :=
    lt_of_le_of_ne (hx a).2 (mem_fractionalSupport.mp haFrac).2
  let rest : Finset A := (rowSet row r).erase a
  have hrest01 : ∀ b ∈ rest, x b = 0 ∨ x b = 1 := by
    intro b hb
    have hbrow : row b = r := by
      exact mem_rowSet.mp (Finset.mem_of_mem_erase hb)
    have hbne : b ≠ a := Finset.ne_of_mem_erase hb
    have hbnotFrac : b ∉ fractionalSupport x := by
      intro hbFrac
      have hbFiber : b ∈ rowFiber (fractionalSupport x) row r :=
        mem_rowFiber.mpr ⟨hbFrac, hbrow⟩
      have : b = a := by simpa only [haFiber, Finset.mem_singleton] using hbFiber
      exact hbne this
    exact eq_zero_or_one_of_not_fractional hbnotFrac
  let ones : Finset A := rest.filter fun b ↦ x b = 1
  have hrestSum : ∑ b ∈ rest, x b = (ones.card : ℝ) := by
    calc
      (∑ b ∈ rest, x b) =
          ∑ b ∈ rest, if x b = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rcases hrest01 b hb with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = ∑ _b ∈ ones, (1 : ℝ) := by
        dsimp only [ones]
        rw [Finset.sum_filter]
      _ = (ones.card : ℝ) := by simp
  have haRowSet : a ∈ rowSet row r := mem_rowSet.mpr harow
  have hrowSplit :
      ∑ b ∈ rowSet row r, x b = (ones.card : ℝ) + x a := by
    rw [← Finset.sum_erase_add _ _ haRowSet]
    simpa only [rest] using congrArg (fun y : ℝ ↦ y + x a) hrestSum
  obtain ⟨k, hk⟩ := hrowInt r
  have hcast : (((k - (ones.card : ℤ)) : ℤ) : ℝ) = x a := by
    push_cast
    linarith [hk, hrowSplit]
  have hkposR : (0 : ℝ) < ((k - (ones.card : ℤ) : ℤ) : ℝ) := by
    rw [hcast]
    exact haxpos
  have hkltR : ((k - (ones.card : ℤ) : ℤ) : ℝ) < 1 := by
    rw [hcast]
    exact haxlt
  have hkpos : (0 : ℤ) < k - (ones.card : ℤ) := by exact_mod_cast hkposR
  have hklt : k - (ones.card : ℤ) < (1 : ℤ) := by exact_mod_cast hkltR
  omega

end

end Erdos390.WholePaper


/-!
# Discrepancy after a column becomes light

Once a column has at most `4*d` still-fractional coordinates, every later
change is supported on those coordinates and has magnitude at most one per
coordinate.  This is the final estimate in the paper's floating-rounding
argument.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section


/-- A zero-one column can change by at most the number of its coordinates in
the set on which changes are still permitted. -/
theorem abs_column_discrepancy_le_card
    {A C : Type*} [Fintype A]
    (F : Finset A) (inc : C → A → Prop) (c : C)
    (x X : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hX : ∀ a, 0 ≤ X a ∧ X a ≤ 1)
    (houtside : ∀ a ∉ F, X a = x a) :
    |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤
      ((columnSupportIn F inc c).card : ℝ) := by
  classical
  let D : Finset A := columnSupportIn F inc c
  have hsum :
      (∑ a, (X a - x a) * zeroOneColumn inc c a) =
        ∑ a ∈ D, (X a - x a) := by
    calc
      (∑ a, (X a - x a) * zeroOneColumn inc c a) =
          ∑ a ∈ (Finset.univ : Finset A),
            ((X a - x a) * zeroOneColumn inc c a) := rfl
      _ = ∑ a ∈ D,
            ((X a - x a) * zeroOneColumn inc c a) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ D)
        intro a _ haD
        by_cases haF : a ∈ F
        · have hnotInc : ¬ inc c a := by
            intro hinc
            exact haD (by
              simpa only [D, mem_columnSupportIn] using And.intro haF hinc)
          simp [zeroOneColumn, hnotInc]
        · simp [zeroOneColumn, houtside a haF]
      _ = ∑ a ∈ D, (X a - x a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hinc : inc c a := (mem_columnSupportIn.mp (by
          simpa only [D] using ha)).2
        simp [zeroOneColumn, hinc]
  rw [hsum]
  calc
    |∑ a ∈ D, (X a - x a)| ≤ ∑ a ∈ D, |X a - x a| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_le]
      constructor <;> linarith [hx a, hX a]
    _ = (D.card : ℝ) := by simp
    _ = ((columnSupportIn F inc c).card : ℝ) := by rfl

end

end Erdos390.WholePaper


/-!
# Column-sparse floating rounding

This is the deterministic floating-rounding lemma used in the final assembly
of the paper.  The proof iterates `exists_floating_step`, retaining all active
row equations and all columns that are still heavy.  A stronger internal
statement records that coordinates which were already integral never move.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Floating rounding with the freezing invariant made explicit. -/
theorem floating_rounding_with_frozen_coordinates
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ a, x a = 0 ∨ x a = 1 → X a = x a) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by
  classical
  generalize hm : (fractionalSupport x).card = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
      by_cases hF : (fractionalSupport x).Nonempty
      · let F : Finset A := fractionalSupport x
        let AR : Finset R := activeRows F row
        let HC : Finset C := heavyColumns F inc d
        let E : Type _ := Sum ↥AR ↥HC
        let w : E → A → ℝ := fun e a ↦ match e with
          | Sum.inl r => zeroOneColumn (fun r' a' ↦ row a' = r') r.1 a
          | Sum.inr c => zeroOneColumn inc c.1 a
        have htwo : ∀ r ∈ activeRows F row,
            2 ≤ (rowFiber F row r).card := by
          simpa only [F] using
            two_le_card_rowFiber_of_integer_rowSums row x hx hrowInt
        have hcount : AR.card + HC.card < F.card := by
          simpa only [AR, HC] using
            card_activeRows_add_heavyColumns_lt F row inc d
              (by simpa only [F] using hF) htwo hsparse
        have hEcard : Fintype.card E < (fractionalSupport x).card := by
          simpa only [E, Fintype.card_sum, Fintype.card_coe, F] using hcount
        obtain ⟨x', hx', hfreezeStep, hpreserve, hdecrease⟩ :=
          exists_floating_step w x hx hEcard
        have hrowWeight (v : A → ℝ) (r : R) :
            (∑ a, zeroOneColumn (fun r' a' ↦ row a' = r') r a * v a) =
              ∑ a ∈ rowSet row r, v a := by
          simp [zeroOneColumn, rowSet, Finset.sum_filter]
        have hrowStep : ∀ r, ∑ a ∈ rowSet row r, x' a =
            ∑ a ∈ rowSet row r, x a := by
          intro r
          by_cases hr : r ∈ AR
          · have hp := hpreserve (Sum.inl (⟨r, hr⟩ : ↥AR))
            rw [← hrowWeight x' r, ← hrowWeight x r]
            simpa only [w] using hp
          · apply Finset.sum_congr rfl
            intro a ha
            have harow : row a = r := mem_rowSet.mp ha
            have haNotF : a ∉ F := by
              intro haF
              exact hr (by
                simpa only [AR, mem_activeRows] using ⟨a, haF, harow⟩)
            have haInt : x a = 0 ∨ x a = 1 := by
              by_contra hnot
              push_neg at hnot
              exact haNotF (by
                simpa only [F, mem_fractionalSupport] using hnot)
            exact hfreezeStep a haInt
        have hrowInt' : ∀ r, ∃ k : ℤ,
            ∑ a ∈ rowSet row r, x' a = (k : ℝ) := by
          intro r
          obtain ⟨k, hk⟩ := hrowInt r
          exact ⟨k, (hrowStep r).trans hk⟩
        have hcolStep (c : C) (hc : c ∈ HC) :
            (∑ a, zeroOneColumn inc c a * x' a) =
              ∑ a, zeroOneColumn inc c a * x a := by
          have hp := hpreserve (Sum.inr (⟨c, hc⟩ : ↥HC))
          simpa only [w] using hp
        have hlt : (fractionalSupport x').card < m := by
          rw [← hm]
          exact hdecrease
        obtain ⟨X, hXInt, hfreezeIH, hrowIH, hcolIH⟩ :=
          ih (fractionalSupport x').card hlt x' hx' hrowInt'
            (rfl : (fractionalSupport x').card =
              (fractionalSupport x').card)
        have hXbounds : ∀ a, 0 ≤ X a ∧ X a ≤ 1 := by
          intro a
          rcases hXInt a with hzero | hone
          · simp [hzero]
          · simp [hone]
        have hfreeze : ∀ a, x a = 0 ∨ x a = 1 → X a = x a := by
          intro a ha
          have hstep : x' a = x a := hfreezeStep a ha
          have ha' : x' a = 0 ∨ x' a = 1 := by
            rw [hstep]
            exact ha
          exact (hfreezeIH a ha').trans hstep
        refine ⟨X, hXInt, hfreeze, ?_, ?_⟩
        · intro r
          exact (hrowIH r).trans (hrowStep r)
        · intro c
          by_cases hc : c ∈ HC
          · have hdiff :
                (∑ a, (X a - x a) * zeroOneColumn inc c a) =
                  ∑ a, (X a - x' a) * zeroOneColumn inc c a := by
              simp only [sub_mul, Finset.sum_sub_distrib]
              have hcstep := hcolStep c hc
              simpa only [mul_comm] using
                (congrArg
                  (fun y : ℝ ↦ (∑ a, X a * zeroOneColumn inc c a) - y)
                  hcstep).symm
            rw [hdiff]
            exact hcolIH c
          · have houtside : ∀ a ∉ F, X a = x a := by
              intro a haF
              have haInt : x a = 0 ∨ x a = 1 := by
                by_contra hnot
                push_neg at hnot
                exact haF (by
                  simpa only [F, mem_fractionalSupport] using hnot)
              exact hfreeze a haInt
            have hlight : (columnSupportIn F inc c).card ≤ 4 * d := by
              have : ¬ 4 * d < (columnSupportIn F inc c).card := by
                simpa only [HC, mem_heavyColumns] using hc
              omega
            calc
              |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤
                  ((columnSupportIn F inc c).card : ℝ) :=
                abs_column_discrepancy_le_card F inc c x X hx hXbounds houtside
              _ ≤ (4 * d : ℝ) := by exact_mod_cast hlight
      · have hnotMem : ∀ a, a ∉ fractionalSupport x := by
          intro a ha
          exact hF ⟨a, ha⟩
        have hInt : ∀ a, x a = 0 ∨ x a = 1 := by
          intro a
          by_contra hnot
          push_neg at hnot
          exact hnotMem a (mem_fractionalSupport.mpr hnot)
        refine ⟨x, hInt, ?_, ?_, ?_⟩
        · intro a _
          rfl
        · intro r
          rfl
        · intro c
          simp

/-- The paper's floating-rounding lemma: all row sums are retained exactly
and every zero-one column incurs discrepancy at most `4*d`. -/
theorem floating_rounding
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by
  obtain ⟨X, hX, _, hrow, hcol⟩ :=
    floating_rounding_with_frozen_coordinates row inc d x hx hrowInt hsparse
  exact ⟨X, hX, hrow, hcol⟩

end

end Erdos390.WholePaper


open Erdos390.WholePaper
theorem solution
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by
  exact floating_rounding row inc d x hx hrowInt hsparse
