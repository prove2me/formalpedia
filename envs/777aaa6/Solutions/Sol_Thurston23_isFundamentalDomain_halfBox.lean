-- Prove2me | solution 1 for Thurston23.isFundamentalDomain_halfBox
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T16:29:44.228968+00:00
-- url     : https://prove2.me/submissions/ab0c6424-a8e5-483d-a30d-bf852025d6cb

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_picard

/-!
The closed half box is a fundamental domain for the Picard group acting effectively: reduction
theory carries every point into the box (a maximal height on the orbit, a translation, and the
inversion if `|q| < 1`), folded by `z ↦ -z`; an element carrying a point of the open box into the
open box is `±1` (the three-dimensional analogue of the argument for the modular domain); and
the boundary, four coordinate planes and the unit sphere, is null. Verbatim from the mission's
source file `Thurston23.lean`, sections `Covolume` (reduction) and `PicardFundamentalDomain`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section Picard

open MatrixGroups Quaternion

theorem entry_mem_of_mem_picard {g : SL(2, ℂ)} (hg : g ∈ picard) (i j : Fin 2) :
    ∃ z : GaussianInt, (z : ℂ) = g i j := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, by simp⟩

theorem mem_picard_iff {g : SL(2, ℂ)} :
    g ∈ picard ↔ ∀ i j, ∃ z : GaussianInt, (z : ℂ) = g i j := by
  refine ⟨entry_mem_of_mem_picard, fun hg => ?_⟩
  choose h hh using hg
  have hdet : (Matrix.of h).det = 1 := by
    apply GaussianInt.toComplex_injective
    rw [RingHom.map_det, map_one]
    convert g.2 using 2
    ext i j
    simp [hh]
  exact ⟨⟨Matrix.of h, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hh]⟩

theorem normSq_coeComplex (z : ℂ) : normSq (z : ℍ) = Complex.normSq z := by
  simp only [normSq_def', re_coeComplex, imI_coeComplex, imJ_coeComplex, imK_coeComplex,
    Complex.normSq_apply]
  ring

/-- `|x + y|² ≤ 2 (|x|² + |y|²)` in the quaternions. -/
theorem normSq_add_le (x y : ℍ) : normSq (x + y) ≤ 2 * (normSq x + normSq y) := by
  simp only [normSq_def', Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.imI - y.imI), sq_nonneg (x.imJ - y.imJ),
    sq_nonneg (x.imK - y.imK)]

/-- On the half-space `|c q + d|² ≥ |c|² t²`: the `j` and `k` parts of `c q + d` are `c t`. -/
theorem normSq_mul_imJ_le (c d : ℂ) {q : ℍ} (hK : q.imK = 0) :
    Complex.normSq c * q.imJ ^ 2 ≤ normSq ((c : ℍ) * q + (d : ℍ)) := by
  simp [normSq_def', hK, Complex.normSq_apply]
  nlinarith [sq_nonneg (c.re * q.re - c.im * q.imI + d.re),
    sq_nonneg (c.re * q.imI + c.im * q.re + d.im)]

/-- A compact subset of `ℍ³` lies in a box: heights in `[t₀, T]` with `t₀ > 0`, and
`|q|² ≤ R`. -/
theorem exists_box_of_isCompact {K : Set H3} (hK : IsCompact K) :
    ∃ t₀ T R : ℝ, 0 < t₀ ∧ ∀ p ∈ K, t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, 0, one_pos, by simp⟩
  have hh : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have hn : Continuous fun p : H3 => normSq (toQ p) := by
    have : (fun p : H3 => normSq (toQ p)) = fun p => ‖toQ p‖ * ‖toQ p‖ :=
      funext fun p => normSq_eq_norm_mul_self _
    rw [this]
    exact (continuous_norm.comp continuous_toQ).mul (continuous_norm.comp continuous_toQ)
  obtain ⟨p₀, -, hmin⟩ := hK.exists_isMinOn hne hh.continuousOn
  obtain ⟨T, hT⟩ := hK.bddAbove_image hh.continuousOn
  obtain ⟨R, hR⟩ := hK.bddAbove_image hn.continuousOn
  exact ⟨p₀.1 2, T, R, p₀.2, fun p hp => ⟨hmin hp, hT ⟨p, hp, rfl⟩, hR ⟨p, hp, rfl⟩⟩⟩

/-- The height of `g • p` is the height of `p` divided by `|c q + d|²`. -/
theorem smul_height (g : SL(2, ℂ)) (p : H3) :
    (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
  (mobiusQ_imJ g (toQ_imK p)).1

/-- If `g` moves a point of the box to a point of the box, then `|c q + d|² ≤ T / t₀`, so
`|c|² ≤ T / t₀³` and `|d|² ≤ 2 (T / t₀ + R T / t₀³)`. -/

theorem finite_gaussianInt_normSq_le (M : ℝ) :
    {w : ℂ | (∃ z : GaussianInt, (z : ℂ) = w) ∧ Complex.normSq w ≤ M}.Finite := by
  have key : ∀ k : ℤ, (k : ℝ) ^ 2 ≤ M → k ∈ Set.Icc (-⌈1 + M⌉) ⌈1 + M⌉ := by
    intro k hk
    have hc := Int.le_ceil (1 + M)
    have h1 : (k : ℝ) ≤ ⌈1 + M⌉ := by nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg (k : ℝ)]
    have h2 : (-⌈1 + M⌉ : ℝ) ≤ k := by nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg (k : ℝ)]
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  refine (((Set.finite_Icc (-⌈1 + M⌉) ⌈1 + M⌉).prod (Set.finite_Icc (-⌈1 + M⌉) ⌈1 + M⌉)).image
    fun x : ℤ × ℤ => ((⟨x.1, x.2⟩ : GaussianInt) : ℂ)).subset ?_
  rintro w ⟨⟨z, rfl⟩, hw⟩
  rw [Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hw
  exact ⟨(z.re, z.im), ⟨key _ (by nlinarith [mul_self_nonneg (z.im : ℝ)]),
    key _ (by nlinarith [mul_self_nonneg (z.re : ℝ)])⟩, rfl⟩

end Picard

section Covolume

open MatrixGroups Quaternion Pointwise

instance : SMulInvariantMeasure SL(2, ℂ) H3 hvol :=
  ⟨fun g _ hs => (measurePreserving_smul g).measure_preimage hs.nullMeasurableSet⟩

instance : MeasurableConstSMul SL(2, ℂ) H3 := ⟨fun g => (continuous_smul g).measurable⟩

theorem normSq_toQ (p : H3) : normSq (toQ p) = N p.1 := by
  rw [normSq_def']; simp [toQ, N]; ring

theorem T_mem_picard (z : GaussianInt) : T (z : ℂ) ∈ picard :=
  mem_picard_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨1, by simp [T]⟩, ⟨z, by simp [T]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [T]⟩, ⟨1, by simp [T]⟩⟩⟩)

theorem S_mem_picard : S ∈ picard :=
  mem_picard_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨0, by simp [S]⟩, ⟨-1, by simp [S]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨1, by simp [S]⟩, ⟨0, by simp [S]⟩⟩⟩)

/-- Along an orbit of the Picard group only finitely many heights are at least the starting
one: they are `t / |c q + d|²` with `|c q + d|² ≤ 1`, which bounds the Gaussian integers `c`
and `d`. -/
theorem finite_heights (p : H3) :
    ((fun g : SL(2, ℂ) => (g • p).1 2) '' {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}).Finite := by
  have ht0 : 0 < p.1 2 := p.2
  refine (((finite_gaussianInt_normSq_le (1 / p.1 2 ^ 2)).prod
    (finite_gaussianInt_normSq_le (2 * (1 + 1 / p.1 2 ^ 2 * normSq (toQ p))))).image
      fun cd : ℂ × ℂ => p.1 2 / normSq ((cd.1 : ℍ) * toQ p + (cd.2 : ℍ))).subset ?_
  rintro _ ⟨g, ⟨hg, hle⟩, rfl⟩
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc
  -- `|c q + d|² ≤ 1`, since the height did not drop
  have hM1 : normSq M ≤ 1 := by
    rw [hh, le_div_iff₀ hMpos] at hle
    nlinarith
  have hcb : Complex.normSq (g 1 0) ≤ 1 / p.1 2 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ 1 / p.1 2 ^ 2 * normSq (toQ p) :=
    mul_le_mul_of_nonneg_right hcb normSq_nonneg
  refine ⟨(g 1 0, g 1 1), ⟨⟨entry_mem_of_mem_picard hg 1 0, hcb⟩,
    ⟨entry_mem_of_mem_picard hg 1 1, by linarith⟩⟩, ?_⟩
  show p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = (g • p).1 2
  rw [hM, hh]

/-- Every orbit of the Picard group has a point of maximal height. -/
theorem exists_max_height (p : H3) :
    ∃ g₀ ∈ picard, ∀ g ∈ picard, (g • p).1 2 ≤ (g₀ • p).1 2 := by
  have h1 : (1 : SL(2, ℂ)) ∈ {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2} :=
    ⟨picard.one_mem, by simp only [one_smul, le_refl]⟩
  have hne : ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}).Nonempty := ⟨_, 1, h1, rfl⟩
  have hbdd := (finite_heights p).bddAbove
  obtain ⟨g₀, ⟨hg₀, -⟩, hmax⟩ := hne.csSup_mem (finite_heights p)
  have hmax' : (g₀ • p).1 2 = sSup ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}) := hmax
  refine ⟨g₀, hg₀, fun g hg => ?_⟩
  rw [hmax']
  by_cases hle : p.1 2 ≤ (g • p).1 2
  · exact le_csSup hbdd ⟨g, ⟨hg, hle⟩, rfl⟩
  · exact (not_le.1 hle).le.trans (le_csSup hbdd ⟨1, h1, by simp only [one_smul]⟩)

/-- The reduction box of the Picard group: `|x|, |y| ≤ ½` and `|q| ≥ 1`. -/
def picardBox : Set H3 := {p | |p.1 0| ≤ 1 / 2 ∧ |p.1 1| ≤ 1 / 2 ∧ 1 ≤ N p.1}

/-- **Reduction.** The Picard group carries every point into the box: take a point of maximal
height on the orbit and translate it into the strip `|x|, |y| ≤ ½`; then `|q| ≥ 1`, since
otherwise `S`, which divides the height by `|q|²`, would raise it further. -/
theorem exists_smul_mem_picardBox (p : H3) : ∃ g ∈ picard, g • p ∈ picardBox := by
  obtain ⟨g₀, hg₀, hmax⟩ := exists_max_height p
  have hg₁ : T ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ) * g₀ ∈
      picard := picard.mul_mem (T_mem_picard _) hg₀
  set g₁ := T ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ) * g₀
    with hg₁def
  have hval : (g₁ • p).1 = (g₀ • p).1 +
      ![((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ).re,
        ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ).im, 0] := by
    rw [hg₁def, mul_smul, T_smul_val]
  have h0 : |(g₁ • p).1 0| ≤ 1 / 2 := by
    rw [hval]
    simpa [GaussianInt.re_toComplex, sub_eq_add_neg] using abs_sub_round ((g₀ • p).1 0)
  have h1 : |(g₁ • p).1 1| ≤ 1 / 2 := by
    rw [hval]
    simpa [GaussianInt.im_toComplex, sub_eq_add_neg] using abs_sub_round ((g₀ • p).1 1)
  have h2 : (g₁ • p).1 2 = (g₀ • p).1 2 := by rw [hval]; simp
  refine ⟨g₁, hg₁, h0, h1, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hS10 : S 1 0 = 1 := by simp [S]
  have hS11 : S 1 1 = 0 := by simp [S]
  have hht : ((S * g₁) • p).1 2 = (g₁ • p).1 2 / N (g₁ • p).1 := by
    rw [mul_smul, smul_height S (g₁ • p), hS10, hS11, coeComplex_one, coeComplex_zero, one_mul,
      add_zero, normSq_toQ]
  have hNpos : 0 < N (g₁ • p).1 := N_pos (g₁ • p).2
  have hle := hmax _ (picard.mul_mem S_mem_picard hg₁)
  rw [hht, h2, div_le_iff₀ hNpos] at hle
  nlinarith [mul_lt_mul_of_pos_left hlt (g₀ • p).2]


end Covolume

section PicardFundamentalDomain

open Set MatrixGroups Quaternion Pointwise


/-- The complex coordinate `x + iy` of a point of `H3`. -/
noncomputable def zc (p : H3) : ℂ := ⟨p.1 0, p.1 1⟩

@[simp] theorem zc_re (p : H3) : (zc p).re = p.1 0 := rfl

@[simp] theorem zc_im (p : H3) : (zc p).im = p.1 1 := rfl

/-- The denominator of the Möbius action, split into its complex and vertical parts:
`|c q + d|² = |c z + d|² + |c|² t²`. -/
theorem normSq_denom (c d : ℂ) (p : H3) :
    normSq ((c : ℍ) * toQ p + (d : ℍ))
      = Complex.normSq (c * zc p + d) + Complex.normSq c * (p.1 2) ^ 2 := by
  simp [normSq_def', toQ, zc, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring



/-- For an integer, the absolute value is at most the square. -/
theorem abs_le_sq_int (n : ℤ) : |n| ≤ n ^ 2 := by
  rcases eq_or_ne n 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |n| := Int.one_le_abs h
    nlinarith [sq_abs n]

/-- In the open box the height satisfies `t² > ½`. -/
theorem sq_height_gt {p : H3} (hp : p ∈ halfBoxOpen) : 1 / 2 < (p.1 2) ^ 2 := by
  obtain ⟨hx, hy0, hy1, hN⟩ := hp
  have hx2 : (p.1 0) ^ 2 < 1 / 4 := by
    have h := abs_lt.1 hx
    nlinarith [h.1, h.2]
  have hy2 : (p.1 1) ^ 2 < 1 / 4 := by nlinarith
  have : 1 < (p.1 0) ^ 2 + (p.1 1) ^ 2 + (p.1 2) ^ 2 := by
    have : N p.1 = p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
    nlinarith [hN]
  nlinarith

/-- If the height does not drop, the bottom-left entry vanishes: the Picard group
has no element carrying a point of the open box to a point of the open box with a
nonzero `c`. -/
theorem bottomLeft_eq_zero_of_le_one {g : SL(2, ℂ)} (hg : g ∈ picard) {p : H3}
    (hp : p ∈ halfBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) :
    g 1 0 = 0 := by
  obtain ⟨c, hc⟩ := entry_mem_of_mem_picard hg 1 0
  obtain ⟨d, hd⟩ := entry_mem_of_mem_picard hg 1 1
  rw [← hc, ← hd, normSq_denom] at hD
  set x := p.1 0 with hxdef
  set y := p.1 1 with hydef
  set t := p.1 2 with htdef
  have ht2 : 1 / 2 < t ^ 2 := sq_height_gt hp
  obtain ⟨hx, hy0, hy1, hN⟩ := hp
  have hxlt : |x| < 1 / 2 := hx
  have hcre : ((c : ℂ)).re = (c.re : ℝ) := by simp
  have hcim : ((c : ℂ)).im = (c.im : ℝ) := by simp
  have hdre : ((d : ℂ)).re = (d.re : ℝ) := by simp
  have hdim : ((d : ℂ)).im = (d.im : ℝ) := by simp
  -- the norm of `c` as an integer
  set n : ℤ := c.re ^ 2 + c.im ^ 2 with hndef
  have hnormc : Complex.normSq (c : ℂ) = (n : ℝ) := by
    rw [Complex.normSq_apply, hcre, hcim, hndef]
    push_cast
    ring
  have hn0 : 0 ≤ n := by positivity
  rw [hnormc] at hD
  -- `|c|² ≥ 2` is impossible: the vertical part alone exceeds 1
  have hnle : n ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt
    nlinarith [Complex.normSq_nonneg ((c : ℂ) * zc p + (d : ℂ))]
  -- `|c| = 1` is impossible: it forces an integer inequality that never holds
  rcases eq_or_lt_of_le hn0 with hn | hn
  · -- n = 0, so c = 0
    have hre : c.re = 0 ∧ c.im = 0 := by
      constructor <;> nlinarith [sq_nonneg c.re, sq_nonneg c.im]
    rw [← hc]
    have : c = 0 := by
      apply Zsqrtd.ext <;> simp [hre.1, hre.2]
    simp [this]
  · exfalso
    have hn1 : n = 1 := by omega
    -- the complex part is smaller than |z|²
    have hz : Complex.normSq ((c : ℂ) * zc p + (d : ℂ)) < x ^ 2 + y ^ 2 := by
      have hNval : N p.1 = x * x + y * y + t * t := rfl
      rw [hn1] at hD
      push_cast at hD
      nlinarith [hN, hNval]
    -- expand: the inequality says `e₁² + e₂² < |e₁| + |e₂|` for integers `e₁, e₂`
    set e1 : ℤ := c.re * d.re + c.im * d.im with he1
    set e2 : ℤ := c.re * d.im - c.im * d.re with he2
    have hsum : (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2 = (d.re : ℝ) ^ 2 + (d.im : ℝ) ^ 2 := by
      have hn1' : (c.re : ℝ) ^ 2 + (c.im : ℝ) ^ 2 = 1 := by
        have : ((c.re ^ 2 + c.im ^ 2 : ℤ) : ℝ) = 1 := by rw [← hndef, hn1]; norm_num
        push_cast at this
        linarith
      push_cast [he1, he2]
      linear_combination ((d.re : ℝ) ^ 2 + (d.im : ℝ) ^ 2) * hn1'
    have hexp : Complex.normSq ((c : ℂ) * zc p + (d : ℂ))
        = x ^ 2 + y ^ 2 + 2 * (x * (e1 : ℝ) + y * (e2 : ℝ)) + ((d.re : ℝ) ^ 2 + (d.im : ℝ) ^ 2) := by
      have hn1' : (c.re : ℝ) ^ 2 + (c.im : ℝ) ^ 2 = 1 := by
        have : ((c.re ^ 2 + c.im ^ 2 : ℤ) : ℝ) = 1 := by rw [← hndef, hn1]; norm_num
        push_cast at this
        linarith
      rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        hcre, hcim, hdre, hdim, zc_re, zc_im]
      push_cast [he1, he2]
      linear_combination (x ^ 2 + y ^ 2) * hn1'
    rw [hexp] at hz
    -- so `e₁² + e₂² < -2(x e₁ + y e₂) ≤ |e₁| + |e₂|`, which fails for integers
    have hkey : ((d.re : ℝ) ^ 2 + (d.im : ℝ) ^ 2) < |(e1 : ℝ)| + |(e2 : ℝ)| := by
      have h1 : |x * (e1 : ℝ)| ≤ (1 / 2) * |(e1 : ℝ)| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hxlt.le (abs_nonneg _)
      have h2 : |y * (e2 : ℝ)| ≤ (1 / 2) * |(e2 : ℝ)| := by
        rw [abs_mul]
        have : |y| ≤ 1 / 2 := by rw [abs_of_pos hy0]; linarith
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      have h3 := neg_abs_le (x * (e1 : ℝ))
      have h4 := neg_abs_le (y * (e2 : ℝ))
      linarith
    rw [← hsum] at hkey
    have hint : |e1| + |e2| ≤ e1 ^ 2 + e2 ^ 2 := add_le_add (abs_le_sq_int e1) (abs_le_sq_int e2)
    have hcast : |(e1 : ℝ)| + |(e2 : ℝ)| ≤ (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2 := by
      rw [← Int.cast_abs, ← Int.cast_abs]
      exact_mod_cast hint
    linarith

/-- A triangular element factors as a rotation-dilation followed by a translation,
with no division: `g = T (b a) * D a`. -/
theorem sl2_eq_of_eq_zero' (g : SL(2, ℂ)) (hc : g 1 0 = 0) (ha : g 0 0 ≠ 0) :
    g = T (g 0 1 * g 0 0) * D (g 0 0) ha := by
  have hdet := sl2_det g
  have hd : g 1 1 = (g 0 0)⁻¹ := by
    rw [hc, mul_zero, sub_zero] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [T, D, Matrix.mul_apply, Fin.sum_univ_two, hc, hd] <;>
    field_simp

/-- The coordinates of a rotation-dilation. -/
theorem D_smul_coord (a : ℂ) (ha : a ≠ 0) (p : H3) :
    (D a ha • p).1 0 = (a.re ^ 2 - a.im ^ 2) * p.1 0 - 2 * (a.re * a.im) * p.1 1 ∧
    (D a ha • p).1 1 = 2 * (a.re * a.im) * p.1 0 + (a.re ^ 2 - a.im ^ 2) * p.1 1 ∧
    (D a ha • p).1 2 = (a.re ^ 2 + a.im ^ 2) * p.1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto
  · rw [D_smul_val]
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    try ring
    try tauto

/-- An element whose matrix is `± 1` acts trivially: `-1` cancels against its
inverse in the Möbius formula. -/
theorem smul_eq_self_of_coe_eq_pm_one {g : SL(2, ℂ)}
    (h : (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1) (q : H3) :
    g • q = q := by
  rcases h with h | h
  · rw [show g = 1 from Subtype.ext h, one_smul]
  · apply toQ_injective
    rw [toQ_smul]
    have e00 : g 0 0 = -1 := by rw [h]; simp [Matrix.one_apply]
    have e01 : g 0 1 = 0 := by rw [h]; simp [Matrix.one_apply]
    have e10 : g 1 0 = 0 := by rw [h]; simp [Matrix.one_apply]
    have e11 : g 1 1 = -1 := by rw [h]; simp [Matrix.one_apply]
    rw [mobiusQ, e00, e01, e10, e11, coe_neg_one]
    simp

/-- **Uniqueness, the triangular case.** If the height does not drop, an element of
the Picard group carrying a point of the open box into the open box fixes it. -/
theorem smul_eq_self_of_le_one {g : SL(2, ℂ)} (hg : g ∈ picard) {p : H3}
    (hp : p ∈ halfBoxOpen) (hgp : g • p ∈ halfBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) :
    ∀ q : H3, g • q = q := by
  have hc : g 1 0 = 0 := bottomLeft_eq_zero_of_le_one hg hp hD
  obtain ⟨A, hA⟩ := entry_mem_of_mem_picard hg 0 0
  obtain ⟨B, hB⟩ := entry_mem_of_mem_picard hg 0 1
  obtain ⟨Dg, hDg⟩ := entry_mem_of_mem_picard hg 1 1
  have hdet := sl2_det g
  rw [hc, mul_zero, sub_zero] at hdet
  have ha0 : g 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have hd0 : g 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  -- `|d|² ≤ 1`, and it is a positive integer, so `|d|² = |a|² = 1`
  have hDval : Complex.normSq (g 1 1) ≤ 1 := by
    have h := hD
    rw [normSq_denom, hc] at h
    simpa using h
  have hDeq : Complex.normSq (g 1 1) = ((Dg.re ^ 2 + Dg.im ^ 2 : ℤ) : ℝ) := by
    rw [← hDg, Complex.normSq_apply, GaussianInt.re_toComplex, GaussianInt.im_toComplex]
    push_cast
    ring
  have hDge : (1 : ℝ) ≤ Complex.normSq (g 1 1) := by
    have hpos : 0 < ((Dg.re ^ 2 + Dg.im ^ 2 : ℤ) : ℝ) := by
      rw [← hDeq]
      exact Complex.normSq_pos.2 hd0
    have h1 : (0 : ℤ) < Dg.re ^ 2 + Dg.im ^ 2 := by exact_mod_cast hpos
    have h2 : ((1 : ℤ) : ℝ) ≤ ((Dg.re ^ 2 + Dg.im ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    rw [hDeq]
    simpa using h2
  have hDone : Complex.normSq (g 1 1) = 1 := le_antisymm hDval hDge
  have hnormA : Complex.normSq (g 0 0) = 1 := by
    have hprod : Complex.normSq (g 0 0) * Complex.normSq (g 1 1) = 1 := by
      rw [← Complex.normSq_mul, hdet, Complex.normSq_one]
    rw [hDone, mul_one] at hprod
    exact hprod
  have hre : (g 0 0).re = (A.re : ℝ) := by rw [← hA, GaussianInt.re_toComplex]
  have him : (g 0 0).im = (A.im : ℝ) := by rw [← hA, GaussianInt.im_toComplex]
  have hsq1 : (g 0 0).re ^ 2 + (g 0 0).im ^ 2 = 1 := by
    have h := hnormA
    rw [Complex.normSq_apply] at h
    nlinarith [h]
  have hsumZ : A.re ^ 2 + A.im ^ 2 = 1 := by
    have h : ((A.re ^ 2 + A.im ^ 2 : ℤ) : ℝ) = 1 := by
      push_cast
      rw [← hre, ← him]
      exact hsq1
    exact_mod_cast h
  -- a unit of `ℤ[i]` has one vanishing component, so the rotation is `z ↦ ± z`
  have hAzero : A.re = 0 ∨ A.im = 0 := by
    rcases eq_or_ne A.re 0 with h | h
    · exact Or.inl h
    · right
      nlinarith [Int.one_le_abs h, sq_abs A.re, sq_nonneg A.im]
  have hprod0 : (g 0 0).re * (g 0 0).im = 0 := by
    rcases hAzero with h | h
    · rw [hre, h]; simp
    · rw [him, h]; simp
  have hs : (g 0 0).re ^ 2 - (g 0 0).im ^ 2 = 1 ∨ (g 0 0).re ^ 2 - (g 0 0).im ^ 2 = -1 := by
    rcases hAzero with h | h
    · right
      have him2 : (g 0 0).im ^ 2 = 1 := by
        have hz : (g 0 0).re = 0 := by rw [hre, h]; simp
        rw [hz] at hsq1
        linarith
      have hz : (g 0 0).re = 0 := by rw [hre, h]; simp
      rw [hz, him2]
      ring
    · left
      have hre2 : (g 0 0).re ^ 2 = 1 := by
        have hz : (g 0 0).im = 0 := by rw [him, h]; simp
        rw [hz] at hsq1
        linarith
      have hz : (g 0 0).im = 0 := by rw [him, h]; simp
      rw [hz, hre2]
      ring
  -- coordinates of `g • p`, translated by the Gaussian integer `b a`
  have hfac : g = T (g 0 1 * g 0 0) * D (g 0 0) ha0 := sl2_eq_of_eq_zero' g hc ha0
  have hbeta : g 0 1 * g 0 0 = ((B * A : GaussianInt) : ℂ) := by
    rw [GaussianInt.toComplex_mul, hA, hB]
  obtain ⟨hD0, hD1, hD2⟩ := D_smul_coord (g 0 0) ha0 p
  have hsmul : g • p = T (g 0 1 * g 0 0) • (D (g 0 0) ha0 • p) := by
    conv_lhs => rw [hfac]
    rw [mul_smul]
  have hx' : (g • p).1 0
      = ((g 0 0).re ^ 2 - (g 0 0).im ^ 2) * p.1 0 + (((B * A).re : ℤ) : ℝ) := by
    rw [hsmul, T_smul_val, hbeta, GaussianInt.re_toComplex]
    simp [hD0, hprod0]
  have hy' : (g • p).1 1
      = ((g 0 0).re ^ 2 - (g 0 0).im ^ 2) * p.1 1 + (((B * A).im : ℤ) : ℝ) := by
    rw [hsmul, T_smul_val, hbeta, GaussianInt.im_toComplex]
    simp [hD1, hprod0]
  obtain ⟨hx, hy0, hy1, -⟩ := hp
  obtain ⟨hxg, hyg0, hyg1, -⟩ := hgp
  rcases hs with hs | hs
  · -- the rotation is trivial, so both translation components vanish
    rw [hs, one_mul] at hx' hy'
    have hm0 : (B * A).re = 0 := by
      have hval : (((B * A).re : ℤ) : ℝ) = (g • p).1 0 - p.1 0 := by rw [hx']; ring
      have hlt : |(((B * A).re : ℤ) : ℝ)| < 1 := by
        rw [hval, abs_lt]
        have h1 := abs_lt.1 hx
        have h2 := abs_lt.1 hxg
        constructor <;> linarith
      have hpair := abs_lt.1 hlt
      have h1 : (B * A).re < 1 := by exact_mod_cast hpair.2
      have h2 : -1 < (B * A).re := by exact_mod_cast hpair.1
      omega
    have hk0 : (B * A).im = 0 := by
      have hval : (((B * A).im : ℤ) : ℝ) = (g • p).1 1 - p.1 1 := by rw [hy']; ring
      have hlt : |(((B * A).im : ℤ) : ℝ)| < 1 := by
        rw [hval, abs_lt]
        constructor <;> linarith
      have hpair := abs_lt.1 hlt
      have h1 : (B * A).im < 1 := by exact_mod_cast hpair.2
      have h2 : -1 < (B * A).im := by exact_mod_cast hpair.1
      omega
    -- the diagonal is real of absolute value one and the off-diagonal vanishes
    have him2 : (g 0 0).im ^ 2 = 0 := by linear_combination (hsq1 - hs) / 2
    have him0 : (g 0 0).im = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 him2
    have hre2 : (g 0 0).re ^ 2 = 1 := by linear_combination (hsq1 + hs) / 2
    have hre1 : (g 0 0).re = 1 ∨ (g 0 0).re = -1 := by
      have h2 : ((g 0 0).re - 1) * ((g 0 0).re + 1) = 0 := by linear_combination hre2
      rcases mul_eq_zero.1 h2 with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hA0 : A ≠ 0 := by
      intro h
      rw [h] at hA
      simp at hA
      exact ha0 hA.symm
    have hB0 : B = 0 := by
      have hBA : B * A = 0 := by
        apply Zsqrtd.ext
        · simpa using hm0
        · simpa using hk0
      rcases mul_eq_zero.1 hBA with h | h
      · exact h
      · exact absurd h hA0
    have hb0 : g 0 1 = 0 := by rw [← hB, hB0]; simp
    have hdinv : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    have h00 : g 0 0 = 1 ∨ g 0 0 = -1 := by
      rcases hre1 with h | h
      · exact Or.inl (Complex.ext (by simpa using h) (by simpa using him0))
      · exact Or.inr (Complex.ext (by simpa using h) (by simpa using him0))
    have hmat : (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
      rcases h00 with h | h
      · refine Or.inl ?_
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.one_apply, h, hb0, hc, hdinv]
      · refine Or.inr ?_
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.one_apply, h, hb0, hc, hdinv]
    exact smul_eq_self_of_coe_eq_pm_one hmat
  · -- `z ↦ -z` would send `0 < y < ½` below the real axis
    exfalso
    rw [hs] at hy'
    have hk1 : (0 : ℝ) < (((B * A).im : ℤ) : ℝ) := by linarith
    have hk2 : (((B * A).im : ℤ) : ℝ) < 1 := by linarith
    have h1 : 0 < (B * A).im := by exact_mod_cast hk1
    have h2 : (B * A).im < 1 := by exact_mod_cast hk2
    omega


/-- **Uniqueness for the Picard group.** An element of the Picard group carrying a
point of the open half box to a point of the open half box fixes it. Together with
the reduction theory of `exists_smul_mem_picardBox`, this says that the closed half
box is a fundamental domain for the Picard group modulo `±1`. -/
theorem smul_eq_self_of_mem_halfBoxOpen {g : SL(2, ℂ)} (hg : g ∈ picard) {p : H3}
    (hp : p ∈ halfBoxOpen) (hgp : g • p ∈ halfBoxOpen) : ∀ q : H3, g • q = q := by
  rcases le_or_gt (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ))) 1 with hD | hD
  · exact smul_eq_self_of_le_one hg hp hgp hD
  -- the height strictly drops, so run the same argument backwards, at `g • p`
  have hginv : g⁻¹ ∈ picard := picard.inv_mem hg
  have hpos : 0 < normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hpos' : 0 < normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g⁻¹) (toQ_imK (g • p)) (g • p).2)
  have h1 : (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    smul_height g p
  have h2 : (g⁻¹ • (g • p)).1 2 = (g • p).1 2 /
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) := smul_height g⁻¹ (g • p)
  rw [inv_smul_smul, h1, div_div] at h2
  have hne : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≠ 0 :=
    ne_of_gt (mul_pos hpos hpos')
  have h3 := (eq_div_iff hne).1 h2
  have hmul : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) = 1 := by
    have h4 : p.1 2 * (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
        normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ))) = p.1 2 * 1 := by
      rw [h3, mul_one]
    exact mul_left_cancel₀ (ne_of_gt p.2) h4
  have hDinv : normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≤ 1 := by
    nlinarith [hmul, hD, hpos, hpos']
  have key : ∀ q : H3, g⁻¹ • q = q :=
    smul_eq_self_of_le_one hginv hgp (by rw [inv_smul_smul]; exact hp) hDinv
  intro q
  have h := key (g • q)
  rw [inv_smul_smul] at h
  exact h.symm


/-- The rotation `z ↦ -z`, that is `diag(i, -i)`, an element of the Picard group. -/
noncomputable def R : SL(2, ℂ) := D Complex.I Complex.I_ne_zero

theorem R_mem_picard : R ∈ picard := by
  refine mem_picard_iff.2 (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨⟨⟨0, 1⟩, ?_⟩, ⟨0, ?_⟩⟩,
    Fin.forall_fin_two.2 ⟨⟨0, ?_⟩, ⟨⟨0, -1⟩, ?_⟩⟩⟩)
  · apply Complex.ext <;> simp [R, D]
  · simp [R, D]
  · simp [R, D]
  · apply Complex.ext <;> simp [R, D, Complex.inv_I]

theorem R_smul_coord (p : H3) :
    (R • p).1 0 = -p.1 0 ∧ (R • p).1 1 = -p.1 1 ∧ (R • p).1 2 = p.1 2 := by
  obtain ⟨h0, h1, h2⟩ := D_smul_coord Complex.I Complex.I_ne_zero p
  refine ⟨?_, ?_, ?_⟩
  · rw [show R = D Complex.I Complex.I_ne_zero from rfl, h0]
    simp
  · rw [show R = D Complex.I Complex.I_ne_zero from rfl, h1]
    simp
  · rw [show R = D Complex.I Complex.I_ne_zero from rfl, h2]
    simp



/-- **H2.** The Picard group carries every point into the closed half box: reduce
into the full box, then fold by `z ↦ -z` if the imaginary part is negative. -/
theorem exists_smul_mem_halfBox (p : H3) : ∃ g ∈ picard, g • p ∈ halfBox := by
  obtain ⟨g, hg, hx, hy, hN⟩ := exists_smul_mem_picardBox p
  rcases le_or_gt 0 ((g • p).1 1) with hy0 | hy0
  · exact ⟨g, hg, hx, hy0, (abs_le.1 hy).2, hN⟩
  · refine ⟨R * g, picard.mul_mem R_mem_picard hg, ?_⟩
    obtain ⟨h0, h1, h2⟩ := R_smul_coord (g • p)
    rw [mul_smul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h0, abs_neg]
      exact hx
    · rw [h1]
      linarith
    · rw [h1]
      have := (abs_le.1 hy).1
      linarith
    · have hNval : ∀ q : H3, N q.1 = q.1 0 * q.1 0 + q.1 1 * q.1 1 + q.1 2 * q.1 2 := fun _ => rfl
      rw [hNval] at hN
      rw [hNval, h0, h1, h2]
      nlinarith [hN]


/-! ### H3, step 1: the boundary of the half box is null -/

/-- A subset of `H3` lying over a Lebesgue-null set of `ℝ³` has hyperbolic volume zero. -/
theorem hvol_preimage_eq_zero {A : Set (Fin 3 → ℝ)} (hA : MeasurableSet A)
    (h : volume A = 0) : hvol (Subtype.val ⁻¹' A) = 0 := by
  have hs : MeasurableSet (Subtype.val ⁻¹' A : Set H3) := measurable_subtype_coe hA
  rw [hvol_apply hs]
  have hsub : Subtype.val '' (Subtype.val ⁻¹' A : Set H3) ⊆ A := Set.image_preimage_subset _ _
  exact setLIntegral_measure_zero _ _ (measure_mono_null hsub h)

/-- A coordinate hyperplane of `ℝ³` is null. -/
theorem volume_coord_eq (i : Fin 3) (c : ℝ) : volume {x : Fin 3 → ℝ | x i = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i c

/-- The unit sphere of `ℝ³` is null: transported to `EuclideanSpace`, where spheres
are null for the Haar measure. -/
theorem volume_normOne : volume {x : Fin 3 → ℝ | N x = 1} = 0 := by
  have hset : {x : Fin 3 → ℝ | N x = 1}
      = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Metric.sphere 0 1 := by
    ext x
    have hNdef : N x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := rfl
    have hN : 0 ≤ N x := by
      rw [hNdef]
      nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (N x) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      rw [hNdef, Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs, sq]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere, dist_zero_right, hnorm]
    constructor
    · intro h
      rw [h, Real.sqrt_one]
    · intro h
      have hsq := Real.sq_sqrt hN
      rw [h] at hsq
      simpa using hsq.symm
  rw [hset, (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    (Metric.isClosed_sphere.measurableSet).nullMeasurableSet]
  exact Measure.addHaar_sphere _ _ _

theorem measurableSet_halfBox : MeasurableSet halfBox := by
  have h0 : Measurable fun p : H3 => p.1 0 := (measurable_pi_apply 0).comp measurable_subtype_coe
  have h1 : Measurable fun p : H3 => p.1 1 := (measurable_pi_apply 1).comp measurable_subtype_coe
  have hN : Measurable fun p : H3 => N p.1 := by
    have : (fun p : H3 => N p.1) = fun p : H3 => p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 :=
      rfl
    rw [this]
    exact (((h0.mul h0).add (h1.mul h1)).add
      (((measurable_pi_apply 2).comp measurable_subtype_coe).mul
        ((measurable_pi_apply 2).comp measurable_subtype_coe)))
  exact ((h0.abs measurableSet_Iic).inter ((h1 measurableSet_Ici).inter
    ((h1 measurableSet_Iic).inter (hN measurableSet_Ici))))

/-- **The boundary of the half box is null.** It lies in four coordinate hyperplanes
and the unit sphere. -/
theorem hvol_halfBox_sdiff_halfBoxOpen : hvol (halfBox \ halfBoxOpen) = 0 := by
  have hsub : halfBox \ halfBoxOpen ⊆
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = 1 / 2}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = -(1 / 2)}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 1 = 0}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 1 = 1 / 2}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) := by
    rintro p ⟨⟨hx, hy0, hy1, hN⟩, hopen⟩
    simp only [halfBoxOpen, Set.mem_setOf_eq, not_and, not_lt] at hopen
    by_cases hx' : |p.1 0| < 1 / 2
    · by_cases hy0' : 0 < p.1 1
      · by_cases hy1' : p.1 1 < 1 / 2
        · have : N p.1 ≤ 1 := hopen hx' hy0' hy1'
          exact Or.inr (le_antisymm this hN)
        · exact Or.inl (Or.inr (le_antisymm hy1 (not_lt.1 hy1')))
      · exact Or.inl (Or.inl (Or.inr (le_antisymm (not_lt.1 hy0') hy0)))
    · rcases abs_le.1 hx with ⟨hle, hge⟩
      rcases lt_or_ge (p.1 0) 0 with hneg | hpos
      · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
        have : |p.1 0| = -p.1 0 := abs_of_neg hneg
        have h2 : (1 : ℝ) / 2 ≤ |p.1 0| := not_lt.1 hx'
        show p.1 0 = -(1 / 2)
        rw [this] at h2
        linarith
      · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
        have : |p.1 0| = p.1 0 := abs_of_nonneg hpos
        have h2 : (1 : ℝ) / 2 ≤ |p.1 0| := not_lt.1 hx'
        show p.1 0 = 1 / 2
        rw [this] at h2
        linarith
  refine measure_mono_null hsub ?_
  have hplane : ∀ (i : Fin 3) (c : ℝ),
      hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x i = c}) = 0 := by
    intro i c
    refine hvol_preimage_eq_zero ?_ (volume_coord_eq i c)
    have hset : {x : Fin 3 → ℝ | x i = c} = (fun f : Fin 3 → ℝ => f i) ⁻¹' {c} := rfl
    rw [hset]
    exact measurable_pi_apply i (measurableSet_singleton c)
  have hsphere : hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) = 0 := by
    refine hvol_preimage_eq_zero ?_ volume_normOne
    have : {x : Fin 3 → ℝ | N x = 1}
        = (fun x : Fin 3 → ℝ => x 0 * x 0 + x 1 * x 1 + x 2 * x 2) ⁻¹' {1} := rfl
    rw [this]
    exact ((((measurable_pi_apply 0).mul (measurable_pi_apply 0)).add
      ((measurable_pi_apply 1).mul (measurable_pi_apply 1))).add
      ((measurable_pi_apply 2).mul (measurable_pi_apply 2))) (measurableSet_singleton 1)
  exact measure_union_null (measure_union_null (measure_union_null (measure_union_null
    (hplane 0 (1 / 2)) (hplane 0 (-(1 / 2)))) (hplane 1 0)) (hplane 1 (1 / 2))) hsphere

/-! ### H3, step 2: the Picard group acting effectively, and the fundamental domain -/



/-- **H3.** The closed half box is a fundamental domain for the Picard group acting
effectively. Covering is `exists_smul_mem_halfBox`; disjointness is uniqueness on
the open box, since the boundary is null. -/
theorem isFundamentalDomain_halfBox : IsFundamentalDomain PicardEff halfBox hvol := by
  refine IsFundamentalDomain.mk'' measurableSet_halfBox.nullMeasurableSet ?_ ?_ ?_
  · filter_upwards with p
    obtain ⟨g, hg, hgp⟩ := exists_smul_mem_halfBox p
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, hgp⟩
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hsub : ((QuotientGroup.mk g : PicardEff) • halfBox) ∩ halfBox ⊆
          ((g : SL(2, ℂ)) • (halfBox \ halfBoxOpen)) ∪ (halfBox \ halfBoxOpen) := by
        rintro p ⟨hp1, hp2⟩
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨hcon1, hcon2⟩ := hcon
        have hopen : p ∈ halfBoxOpen := by
          by_contra h
          exact hcon2 ⟨hp2, h⟩
        have hinv : (g : SL(2, ℂ))⁻¹ • p ∈ halfBox := by
          rw [PicardEff.mk_smul_set, Set.mem_smul_set_iff_inv_smul_mem] at hp1
          exact hp1
        have hinvopen : (g : SL(2, ℂ))⁻¹ • p ∈ halfBoxOpen := by
          by_contra h
          refine hcon1 ?_
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          exact ⟨hinv, h⟩
        have htriv : ∀ r : H3, (g : SL(2, ℂ))⁻¹ • r = r :=
          smul_eq_self_of_mem_halfBoxOpen (picard.inv_mem g.2) hopen hinvopen
        have htrivg : ∀ r : H3, (g : SL(2, ℂ)) • r = r := by
          intro r
          have h := htriv ((g : SL(2, ℂ)) • r)
          rw [inv_smul_smul] at h
          exact h.symm
        refine hq ?_
        refine (QuotientGroup.eq_one_iff _).2 ?_
        rw [picardKer, MonoidHom.mem_ker]
        refine Equiv.ext fun r => ?_
        exact htrivg r
      refine measure_mono_null hsub ?_
      refine measure_union_null ?_ hvol_halfBox_sdiff_halfBoxOpen
      rw [measure_smul]
      exact hvol_halfBox_sdiff_halfBoxOpen
  · intro q
    exact (PicardEff.measurePreserving q).quasiMeasurePreserving


end PicardFundamentalDomain

end Thurston23

open MeasureTheory in
theorem solution :
    MeasureTheory.IsFundamentalDomain Thurston23.PicardEff Thurston23.halfBox Thurston23.hvol :=
  Thurston23.isFundamentalDomain_halfBox
