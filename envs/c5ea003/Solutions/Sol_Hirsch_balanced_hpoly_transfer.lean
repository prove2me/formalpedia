-- Prove2me | solution 1 for Hirsch.balanced_hpoly_transfer
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T05:10:48.347308+00:00
-- url     : https://prove2.me/submissions/58c28d38-c243-40b1-9acd-85d5abe56dd1

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch WithLp EuclideanSpace

noncomputable section

namespace HirschWedge

variable {d n : ℕ}

/-- Concatenate a last coordinate onto a vector in `ℝ^d`. -/
def embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  toLp 2 (Fin.snoc (ofLp x) t)

/-- Drop the last coordinate. -/
def proj (z : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (Fin.init (ofLp z))

lemma embed_castSucc (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    embed x t i.castSucc = x i := by
  simp [embed, Fin.snoc_castSucc]

lemma embed_last (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    embed x t (Fin.last d) = t := by
  simp [embed, Fin.snoc_last]

lemma proj_apply (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    proj z i = z i.castSucc := by
  rw [proj, PiLp.toLp_apply]
  rfl

lemma proj_embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : proj (embed x t) = x := by
  ext i
  rw [proj_apply, embed_castSucc]

lemma proj_add (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    proj (x + y) = proj x + proj y := by
  ext i
  simp [proj_apply]

lemma proj_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    proj (c • x) = c • proj x := by
  ext i
  simp [proj_apply]

lemma embed_proj (z : EuclideanSpace ℝ (Fin (d + 1))) :
    embed (proj z) (z (Fin.last d)) = z := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [embed_last]
  · intro j
    simp [embed_castSucc, proj_apply]

lemma embed_add (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    embed (x + y) (t + s) = embed x t + embed y s := by
  refine PiLp.ext fun i => ?_
  simp only [embed, ofLp_add, PiLp.toLp_apply, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.add_apply]

lemma embed_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    embed (c • x) (c * t) = c • embed x t := by
  refine PiLp.ext fun i => ?_
  simp only [embed, ofLp_smul, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

lemma embed_neg (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    embed (-x) (-t) = -embed x t := by
  simpa using embed_smul (-1) x t

lemma embed_sub (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    embed (x - y) (t - s) = embed x t - embed y s := by
  simp [sub_eq_add_neg, embed_add, embed_neg]

lemma embed_affine (p q : ℝ) (_hpq : p + q = 1) (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    embed (p • x + q • y) (p * t + q * s) = p • embed x t + q • embed y s := by
  rw [embed_add, embed_smul, embed_smul]

lemma embed_mid (x : EuclideanSpace ℝ (Fin d)) (t ε : ℝ) :
    (1 / 2 : ℝ) • embed x (t - ε) + (1 / 2 : ℝ) • embed x (t + ε) = embed x t := by
  have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
  have hx : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by
    rw [← add_smul, hsum, one_smul]
  have ht : (1 / 2 : ℝ) * (t - ε) + (1 / 2 : ℝ) * (t + ε) = t := by ring
  rw [← embed_affine (1 / 2) (1 / 2) hsum, hx, ht]

lemma weighted_const (α β c : ℝ) (h : α + β = 1) : α * c + β * c = c := by
  simp [← add_mul, h]

lemma inner_embed (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    ⟪embed x t, embed y s⟫ = ⟪x, y⟫ + t * s := by
  simp [embed, inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma embed_injective {x y : EuclideanSpace ℝ (Fin d)} {t s : ℝ}
    (h : embed x t = embed y s) : x = y ∧ t = s := by
  constructor
  · simpa [proj_embed] using congrArg proj h
  · simpa [embed_last] using
      congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) h

lemma last_add (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    (p + q) (Fin.last d) = p (Fin.last d) + q (Fin.last d) :=
  rfl

lemma last_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin (d + 1))) :
    (c • p) (Fin.last d) = c * p (Fin.last d) := by
  simp [smul_eq_mul]

lemma last_affine (p q : EuclideanSpace ℝ (Fin (d + 1))) (α β : ℝ) :
    (α • p + β • q) (Fin.last d) = α * p (Fin.last d) + β * q (Fin.last d) := by
  simp [last_add, last_smul]

lemma last_midpoint (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    (midpoint ℝ p q) (Fin.last d) = (p (Fin.last d) + q (Fin.last d)) / 2 := by
  simp [midpoint_eq_smul_add, last_add, last_smul]
  ring

lemma convex_Hpoly (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy u v hu hv huv i
  have : ⟪a i, u • x + v • y⟫ = u * ⟪a i, x⟫ + v * ⟪a i, y⟫ := by
    simp [inner_add_right, inner_smul_right]
  have : u * ⟪a i, x⟫ + v * ⟪a i, y⟫ ≤ u * b i + v * b i :=
    add_le_add (mul_le_mul_of_nonneg_left (hx i) hu)
      (mul_le_mul_of_nonneg_left (hy i) hv)
  have : u * b i + v * b i = b i := by simp [← add_mul, huv]
  linarith

/-! ## Padding -/

def padA (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    Fin (2 * d) → EuclideanSpace ℝ (Fin d) :=
  fun i => if h : (i : ℕ) < n then a ⟨i, h⟩ else 0

def padB (b : Fin n → ℝ) : Fin (2 * d) → ℝ :=
  fun i => if h : (i : ℕ) < n then b ⟨i, h⟩ else 1

lemma hpoly_pad (hn : n ≤ 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Hpoly (padA a) (padB b) = Hpoly a b := by
  ext x
  simp only [Hpoly, mem_setOf_eq, padA, padB]
  constructor
  · intro h i
    have hi : (i : ℕ) < 2 * d := lt_of_lt_of_le i.isLt hn
    simpa [i.isLt] using h ⟨i, hi⟩
  · intro h i
    by_cases hi : (i : ℕ) < n
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi, inner_zero_left]

/-! ## One-step wedge description -/

def wedgeA (a : Fin n → EuclideanSpace ℝ (Fin d)) (i0 : Fin n) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  Fin.snoc (fun i => embed (a i) (if i = i0 then (1 : ℝ) else 0)) (embed 0 (-1))

def wedgeB (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc b 0

lemma wedgeA_castSucc (a : Fin n → EuclideanSpace ℝ (Fin d)) (i0 : Fin n) (i : Fin n) :
    wedgeA a i0 i.castSucc = embed (a i) (if i = i0 then (1 : ℝ) else 0) := by
  simp [wedgeA, Fin.snoc_castSucc]

lemma wedgeA_last (a : Fin n → EuclideanSpace ℝ (Fin d)) (i0 : Fin n) :
    wedgeA a i0 (Fin.last n) = embed 0 (-1) := by
  simp [wedgeA, Fin.snoc_last]

lemma wedgeB_castSucc (b : Fin n → ℝ) (i : Fin n) : wedgeB b i.castSucc = b i := by
  simp [wedgeB, Fin.snoc_castSucc]

lemma wedgeB_last (b : Fin n → ℝ) : wedgeB b (Fin.last n) = 0 := by
  simp [wedgeB, Fin.snoc_last]

lemma mem_hpoly_embed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    embed x t ∈ Hpoly (wedgeA a i0) (wedgeB b) ↔
      x ∈ Hpoly a b ∧ 0 ≤ t ∧ t ≤ b i0 - ⟪a i0, x⟫ := by
  constructor
  · intro h
    have ht : 0 ≤ t := by
      have := h (Fin.last n)
      simp [wedgeA_last, wedgeB_last, inner_embed, inner_zero_left] at this
      linarith
    have hi (i : Fin n) : ⟪a i, x⟫ + (if i = i0 then t else 0) ≤ b i := by
      have := h i.castSucc
      simpa [wedgeA_castSucc, wedgeB_castSucc, inner_embed, mul_ite, mul_one, mul_zero] using this
    refine ⟨fun i => ?_, ht, ?_⟩
    · have := hi i
      split_ifs at this <;> linarith
    · have := hi i0
      simp at this
      linarith
  · intro hx i
    refine Fin.lastCases ?_ ?_ i
    · simp [wedgeA_last, wedgeB_last, inner_embed, inner_zero_left]
      linarith [hx.2.1]
    · intro j
      simp [wedgeA_castSucc, wedgeB_castSucc, inner_embed, mul_ite, mul_one, mul_zero]
      split_ifs with hj
      · subst hj
        linarith [hx.1 j, hx.2.2]
      · simpa using hx.1 j

lemma slack_nonneg (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) :
    0 ≤ b i0 - ⟪a i0, x⟫ := by
  have := hx i0
  linarith

lemma embed_mem_of_mem (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) :
    embed x 0 ∈ Hpoly (wedgeA a i0) (wedgeB b) :=
  (mem_hpoly_embed a b i0 x 0).2 ⟨hx, le_rfl, slack_nonneg a b i0 hx⟩

lemma embed_mem_upper (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) :
    embed x (b i0 - ⟪a i0, x⟫) ∈ Hpoly (wedgeA a i0) (wedgeB b) :=
  (mem_hpoly_embed a b i0 x (b i0 - ⟪a i0, x⟫)).2 ⟨hx, slack_nonneg a b i0 hx, le_rfl⟩

lemma wedge_nonempty (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) (hne : (Hpoly a b).Nonempty) :
    (Hpoly (wedgeA a i0) (wedgeB b)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨embed x 0, embed_mem_of_mem a b i0 hx⟩

lemma norm_embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖embed x t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  have hx : ‖embed x t‖ ^ 2 = ⟪embed x t, embed x t⟫ :=
    (real_inner_self_eq_norm_sq (embed x t)).symm
  have hy : ‖x‖ ^ 2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
  rw [hx, inner_embed, hy]
  ring

lemma wedge_bounded (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i0 : Fin n) (hbd : Bornology.IsBounded (Hpoly a b)) :
    Bornology.IsBounded (Hpoly (wedgeA a i0) (wedgeB b)) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hC' : ∀ x ∈ Hpoly a b, ‖x‖ ≤ C0 := fun x hx => (hC x hx).trans (le_max_left _ _)
  let T : ℝ := |b i0| + ‖a i0‖ * C0
  have hT : 0 ≤ T := add_nonneg (abs_nonneg _) (mul_nonneg (norm_nonneg _) hC0)
  refine (isBounded_iff_forall_norm_le).2 ⟨Real.sqrt (C0 ^ 2 + T ^ 2), fun z hz => ?_⟩
  have hz' := (mem_hpoly_embed a b i0 (proj z) (z (Fin.last d))).1
    (by simpa [embed_proj] using hz)
  set x := proj z
  set t := z (Fin.last d)
  have hxC : ‖x‖ ≤ C0 := hC' x hz'.1
  have ht0 : 0 ≤ t := hz'.2.1
  have htT : t ≤ T := by
    have : t ≤ b i0 - ⟪a i0, x⟫ := hz'.2.2
    have : b i0 - ⟪a i0, x⟫ ≤ |b i0| + |⟪a i0, x⟫| := by
      have hb : b i0 ≤ |b i0| := le_abs_self _
      have hi : -⟪a i0, x⟫ ≤ |⟪a i0, x⟫| := neg_le_abs _
      linarith
    have : |⟪a i0, x⟫| ≤ ‖a i0‖ * ‖x‖ := abs_real_inner_le_norm _ _
    have : ‖a i0‖ * ‖x‖ ≤ ‖a i0‖ * C0 := mul_le_mul_of_nonneg_left hxC (norm_nonneg _)
    linarith
  have hzid : z = embed x t := (embed_proj z).symm
  have hsq : ‖z‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by simpa [hzid] using norm_embed x t
  have hsq_le : ‖z‖ ^ 2 ≤ C0 ^ 2 + T ^ 2 := by
    have hx2 : ‖x‖ ^ 2 ≤ C0 ^ 2 := by nlinarith [hxC, norm_nonneg x, hC0]
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [htT, ht0, hT]
    nlinarith
  have : 0 ≤ C0 ^ 2 + T ^ 2 := by nlinarith [hC0, hT]
  rw [← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt hsq_le

/-! ## Vertices and edges of the wedge -/

lemma last_eq_bound {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ} {i0 : Fin n}
    {z : EuclideanSpace ℝ (Fin (d + 1))}
    (hz : z ∈ extremePoints ℝ (Hpoly (wedgeA a i0) (wedgeB b))) :
    z (Fin.last d) = 0 ∨ z (Fin.last d) = b i0 - ⟪a i0, proj z⟫ := by
  have hzW : z ∈ Hpoly (wedgeA a i0) (wedgeB b) := hz.1
  have hz' := (mem_hpoly_embed a b i0 (proj z) (z (Fin.last d))).1
    (by simpa [embed_proj] using hzW)
  set x := proj z
  set t := z (Fin.last d)
  by_contra h
  have ht0 : 0 < t := lt_of_le_of_ne hz'.2.1 (Ne.symm (by tauto))
  have hth : t < b i0 - ⟪a i0, x⟫ := lt_of_le_of_ne hz'.2.2 (by tauto)
  let ε : ℝ := min t ((b i0 - ⟪a i0, x⟫) - t) / 2
  have hε : 0 < ε := by
    have : 0 < min t ((b i0 - ⟪a i0, x⟫) - t) := lt_min ht0 (sub_pos.2 hth)
    positivity
  have hmin0 : 0 ≤ min t ((b i0 - ⟪a i0, x⟫) - t) :=
    le_min ht0.le (sub_nonneg.2 hth.le)
  have hε_le : ε ≤ (b i0 - ⟪a i0, x⟫) - t :=
    (half_le_self hmin0).trans (min_le_right _ _)
  have hε_le_t : ε ≤ t := (half_le_self hmin0).trans (min_le_left _ _)
  have hup : embed x (t + ε) ∈ Hpoly (wedgeA a i0) (wedgeB b) := by
    refine (mem_hpoly_embed a b i0 x (t + ε)).2 ⟨hz'.1, by linarith [hz'.2.1, hε.le], ?_⟩
    linarith
  have hdn : embed x (t - ε) ∈ Hpoly (wedgeA a i0) (wedgeB b) := by
    refine (mem_hpoly_embed a b i0 x (t - ε)).2 ⟨hz'.1, by linarith [hε_le_t], ?_⟩
    linarith [hz'.2.2]
  have hzid : z = embed x t := (embed_proj z).symm
  have hop : z ∈ openSegment ℝ (embed x (t - ε)) (embed x (t + ε)) :=
    ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by positivity, by positivity, by ring,
      by rw [embed_mid]; exact hzid.symm⟩
  have heq : embed x (t - ε) = z := hz.2 hdn hup hop
  have : t - ε = t := (embed_injective (heq.trans hzid)).2
  linarith

lemma proj_extreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i0 : Fin n)
    {z : EuclideanSpace ℝ (Fin (d + 1))}
    (hz : z ∈ extremePoints ℝ (Hpoly (wedgeA a i0) (wedgeB b))) :
    proj z ∈ extremePoints ℝ (Hpoly a b) := by
  have hzW : z ∈ Hpoly (wedgeA a i0) (wedgeB b) := hz.1
  have hz' := (mem_hpoly_embed a b i0 (proj z) (z (Fin.last d))).1
    (by simpa [embed_proj] using hzW)
  set x := proj z
  set t := z (Fin.last d)
  refine ⟨hz'.1, ?_⟩
  intro x1 hx1 x2 hx2 hxopen
  obtain ⟨p, q, hp, hq, hpq, hxcomb⟩ := hxopen
  have hzid : z = embed x t := (embed_proj z).symm
  rcases last_eq_bound hz with ht0 | hth
  · have h1 : embed x1 0 ∈ Hpoly (wedgeA a i0) (wedgeB b) := embed_mem_of_mem a b i0 hx1
    have h2 : embed x2 0 ∈ Hpoly (wedgeA a i0) (wedgeB b) := embed_mem_of_mem a b i0 hx2
    have hcomb : z = p • embed x1 0 + q • embed x2 0 := by
      calc
        z = embed x 0 := by
          rw [hzid]
          exact congrArg (embed x) ht0
        _ = embed (p • x1 + q • x2) (p * 0 + q * 0) := by simp [hxcomb]
        _ = p • embed x1 0 + q • embed x2 0 := embed_affine p q hpq x1 x2 0 0
    have hop : z ∈ openSegment ℝ (embed x1 0) (embed x2 0) :=
      ⟨p, q, hp, hq, hpq, hcomb.symm⟩
    have : embed x1 0 = z := hz.2 h1 h2 hop
    simpa [proj_embed] using congrArg proj this
  · have h1 := embed_mem_upper a b i0 hx1
    have h2 := embed_mem_upper a b i0 hx2
    have haff : b i0 - ⟪a i0, p • x1 + q • x2⟫ =
        p * (b i0 - ⟪a i0, x1⟫) + q * (b i0 - ⟪a i0, x2⟫) := by
      simp [inner_add_right, inner_smul_right, mul_sub]
      linarith [weighted_const p q (b i0) hpq]
    have haff' : b i0 - ⟪a i0, x⟫ =
        p * (b i0 - ⟪a i0, x1⟫) + q * (b i0 - ⟪a i0, x2⟫) := by
      simpa [hxcomb] using haff
    have hcomb : z = p • embed x1 (b i0 - ⟪a i0, x1⟫) +
        q • embed x2 (b i0 - ⟪a i0, x2⟫) := by
      calc
        z = embed x (b i0 - ⟪a i0, x⟫) := by
          rw [hzid]
          exact congrArg (embed x) hth
        _ = embed (p • x1 + q • x2)
              (p * (b i0 - ⟪a i0, x1⟫) + q * (b i0 - ⟪a i0, x2⟫)) := by
            rw [hxcomb, haff']
        _ = p • embed x1 (b i0 - ⟪a i0, x1⟫) +
              q • embed x2 (b i0 - ⟪a i0, x2⟫) :=
            embed_affine p q hpq x1 x2 (b i0 - ⟪a i0, x1⟫) (b i0 - ⟪a i0, x2⟫)
    have hop : z ∈ openSegment ℝ (embed x1 (b i0 - ⟪a i0, x1⟫))
        (embed x2 (b i0 - ⟪a i0, x2⟫)) :=
      ⟨p, q, hp, hq, hpq, hcomb.symm⟩
    have : embed x1 (b i0 - ⟪a i0, x1⟫) = z := hz.2 h1 h2 hop
    simpa [proj_embed] using congrArg proj this

lemma bottom_extreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i0 : Fin n)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    embed x 0 ∈ extremePoints ℝ (Hpoly (wedgeA a i0) (wedgeB b)) := by
  refine ⟨embed_mem_of_mem a b i0 hx.1, ?_⟩
  intro z1 hz1 z2 hz2 hop
  obtain ⟨p, q, hp, hq, hpq, hcomb⟩ := hop
  have hz1' := (mem_hpoly_embed a b i0 (proj z1) (z1 (Fin.last d))).1
    (by simpa [embed_proj] using hz1)
  have hz2' := (mem_hpoly_embed a b i0 (proj z2) (z2 (Fin.last d))).1
    (by simpa [embed_proj] using hz2)
  have hlast : p * z1 (Fin.last d) + q * z2 (Fin.last d) = 0 := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) hcomb
    simpa [embed_last, last_affine] using h
  have hz10 : z1 (Fin.last d) = 0 := by
    have h1 : 0 ≤ z1 (Fin.last d) := hz1'.2.1
    have h2 : 0 ≤ z2 (Fin.last d) := hz2'.2.1
    nlinarith
  have hproj_comb : x = p • proj z1 + q • proj z2 := by
    have h := congrArg proj hcomb
    simpa [proj_embed, proj_add, proj_smul] using h.symm
  have hopP : x ∈ openSegment ℝ (proj z1) (proj z2) :=
    ⟨p, q, hp, hq, hpq, hproj_comb.symm⟩
  have hx1 : proj z1 = x := hx.2 hz1'.1 hz2'.1 hopP
  have hz1id : z1 = embed (proj z1) 0 := by simpa [hz10] using (embed_proj z1).symm
  rw [hz1id, hx1]

lemma slack_affine (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i0 : Fin n)
    (p q : EuclideanSpace ℝ (Fin (d + 1))) (α β : ℝ) (hαβ : α + β = 1) :
    b i0 - ⟪a i0, proj (α • p + β • q)⟫ - (α • p + β • q) (Fin.last d) =
      α * (b i0 - ⟪a i0, proj p⟫ - p (Fin.last d)) +
        β * (b i0 - ⟪a i0, proj q⟫ - q (Fin.last d)) := by
  simp [proj_add, proj_smul, inner_add_right, inner_smul_right, last_affine, mul_sub]
  linarith [weighted_const α β (b i0) hαβ]

set_option maxHeartbeats 800000 in
lemma proj_adj (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i0 : Fin n)
    {p q : EuclideanSpace ℝ (Fin (d + 1))}
    (hadj : Adj (Hpoly (wedgeA a i0) (wedgeB b)) p q) :
    proj p = proj q ∨ Adj (Hpoly a b) (proj p) (proj q) := by
  obtain ⟨hpq, hextr⟩ := hadj
  by_cases hproj : proj p = proj q
  · exact Or.inl hproj
  · refine Or.inr ⟨hproj, ?_⟩
    have hpW : p ∈ Hpoly (wedgeA a i0) (wedgeB b) := hextr.subset (left_mem_segment _ _ _)
    have hqW : q ∈ Hpoly (wedgeA a i0) (wedgeB b) := hextr.subset (right_mem_segment _ _ _)
    have hp' := (mem_hpoly_embed a b i0 (proj p) (p (Fin.last d))).1
      (by simpa [embed_proj] using hpW)
    have hq' := (mem_hpoly_embed a b i0 (proj q) (q (Fin.last d))).1
      (by simpa [embed_proj] using hqW)
    have hsegP : segment ℝ (proj p) (proj q) ⊆ Hpoly a b :=
      (convex_Hpoly a b).segment_subset hp'.1 hq'.1
    let m := midpoint ℝ p q
    have hmseg : m ∈ segment ℝ p q := midpoint_mem_segment _ _
    have hmW : m ∈ Hpoly (wedgeA a i0) (wedgeB b) := hextr.subset hmseg
    have hm' := (mem_hpoly_embed a b i0 (proj m) (m (Fin.last d))).1
      (by simpa [embed_proj] using hmW)
    have hm_bound : m (Fin.last d) = 0 ∨
        m (Fin.last d) = b i0 - ⟪a i0, proj m⟫ := by
      by_contra h
      have ht0 : 0 < m (Fin.last d) := lt_of_le_of_ne hm'.2.1 (Ne.symm (by tauto))
      have hth : m (Fin.last d) < b i0 - ⟪a i0, proj m⟫ :=
        lt_of_le_of_ne hm'.2.2 (by tauto)
      let ε : ℝ := min (m (Fin.last d)) ((b i0 - ⟪a i0, proj m⟫) - m (Fin.last d)) / 2
      have hε : 0 < ε := by
        have : 0 < min (m (Fin.last d)) ((b i0 - ⟪a i0, proj m⟫) - m (Fin.last d)) :=
          lt_min ht0 (sub_pos.2 hth)
        positivity
      have hmin0 : 0 ≤ min (m (Fin.last d))
          ((b i0 - ⟪a i0, proj m⟫) - m (Fin.last d)) :=
        le_min ht0.le (sub_nonneg.2 hth.le)
      have hε_le : ε ≤ (b i0 - ⟪a i0, proj m⟫) - m (Fin.last d) :=
        (half_le_self hmin0).trans (min_le_right _ _)
      have hε_le_t : ε ≤ m (Fin.last d) :=
        (half_le_self hmin0).trans (min_le_left _ _)
      let mup := embed (proj m) (m (Fin.last d) + ε)
      let mdn := embed (proj m) (m (Fin.last d) - ε)
      have hup : mup ∈ Hpoly (wedgeA a i0) (wedgeB b) := by
        refine (mem_hpoly_embed a b i0 (proj m) (m (Fin.last d) + ε)).2
          ⟨hm'.1, by linarith [hm'.2.1, hε.le], ?_⟩
        linarith
      have hdn : mdn ∈ Hpoly (wedgeA a i0) (wedgeB b) := by
        refine (mem_hpoly_embed a b i0 (proj m) (m (Fin.last d) - ε)).2
          ⟨hm'.1, by linarith [hε_le_t], ?_⟩
        linarith [hm'.2.2]
      have hm_id : m = embed (proj m) (m (Fin.last d)) := (embed_proj m).symm
      have hop : m ∈ openSegment ℝ mdn mup :=
        ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by positivity, by positivity, by ring,
          by rw [embed_mid]; exact hm_id.symm⟩
      have hupseg : mup ∈ segment ℝ p q :=
        hextr.right_mem_of_mem_openSegment hdn hup hmseg hop
      obtain ⟨α, β, hα, hβ, hαβ, hmup⟩ := hupseg
      have hβeq : β = 1 - α := by linarith
      have hproj_eq : α • proj p + β • proj q =
          (1 / 2 : ℝ) • proj p + (1 / 2 : ℝ) • proj q := by
        have h1 : proj mup = α • proj p + β • proj q := by
          have := congrArg proj hmup.symm
          simpa [mup, proj_embed, proj_add, proj_smul] using this
        have h2 : proj m = (1 / 2 : ℝ) • proj p + (1 / 2 : ℝ) • proj q := by
          simp [m, midpoint_eq_smul_add, proj_add, proj_smul]
        have : proj mup = proj m := by simp [mup, proj_embed]
        rw [← h1, this, h2]
      have huniq : α = (1 / 2 : ℝ) := by
        rw [hβeq] at hproj_eq
        obtain ⟨i, hi⟩ : ∃ i, proj p i ≠ proj q i := by
          by_contra h
          push_neg at h
          exact hproj (PiLp.ext h)
        have hi_eq : α * proj p i + (1 - α) * proj q i =
            (1 / 2) * proj p i + (1 / 2) * proj q i := by
          have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hproj_eq
          simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
        have : (α - 1 / 2) * (proj p i - proj q i) = 0 := by linarith
        have : α - 1 / 2 = 0 :=
          (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hi)
        linarith
      have : mup = m := by
        have hβ2 : β = (1 / 2 : ℝ) := by linarith
        have hm' : m = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q := by
          simp [m, midpoint_eq_smul_add]
        rw [huniq, hβ2, ← hm'] at hmup
        exact hmup.symm
      have : m (Fin.last d) + ε = m (Fin.last d) := by
        simpa [mup, embed_last] using
          congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) this
      linarith
    have hsec : (∀ z ∈ segment ℝ p q, z (Fin.last d) = 0) ∨
        (∀ z ∈ segment ℝ p q, z (Fin.last d) = b i0 - ⟪a i0, proj z⟫) := by
      cases hm_bound with
      | inl h0 =>
        refine Or.inl ?_
        intro z hz
        obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
        have havg : (p (Fin.last d) + q (Fin.last d)) / 2 = 0 := by
          have := last_midpoint p q
          linarith
        have hp0 : p (Fin.last d) = 0 := by
          have hpnn : 0 ≤ p (Fin.last d) := hp'.2.1
          have hqnn : 0 ≤ q (Fin.last d) := hq'.2.1
          nlinarith
        have hq0 : q (Fin.last d) = 0 := by
          have hpnn : 0 ≤ p (Fin.last d) := hp'.2.1
          have hqnn : 0 ≤ q (Fin.last d) := hq'.2.1
          nlinarith
        simp [last_affine, hp0, hq0]
      | inr hh =>
        refine Or.inr ?_
        intro z hz
        obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
        have gp : 0 ≤ b i0 - ⟪a i0, proj p⟫ - p (Fin.last d) := by linarith [hp'.2.2]
        have gq : 0 ≤ b i0 - ⟪a i0, proj q⟫ - q (Fin.last d) := by linarith [hq'.2.2]
        have hm_id : m = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q := by
          simp [m, midpoint_eq_smul_add]
        have hzero : (b i0 - ⟪a i0, proj m⟫) - m (Fin.last d) = 0 := by linarith
        have haff0 := slack_affine a b i0 p q (1 / 2) (1 / 2) (by ring)
        have gmid : (1 / 2 : ℝ) * (b i0 - ⟪a i0, proj p⟫ - p (Fin.last d)) +
            (1 / 2 : ℝ) * (b i0 - ⟪a i0, proj q⟫ - q (Fin.last d)) = 0 := by
          have h := haff0
          rw [← hm_id] at h
          linarith [h, hzero]
        have gp0 : b i0 - ⟪a i0, proj p⟫ - p (Fin.last d) = 0 := by nlinarith
        have gq0 : b i0 - ⟪a i0, proj q⟫ - q (Fin.last d) = 0 := by nlinarith
        have haff := slack_affine a b i0 p q α β hαβ
        have : b i0 - ⟪a i0, proj (α • p + β • q)⟫ -
            (α • p + β • q) (Fin.last d) = 0 := by
          simpa [gp0, gq0] using haff
        linarith
    refine ⟨hsegP, ?_⟩
    intro r hr s hs z hz hzopen
    cases hsec with
    | inl hbot =>
      have hp0 : p (Fin.last d) = 0 := hbot p (left_mem_segment _ _ _)
      have hq0 : q (Fin.last d) = 0 := hbot q (right_mem_segment _ _ _)
      have hp_id : p = embed (proj p) 0 := by simpa [hp0] using (embed_proj p).symm
      have hq_id : q = embed (proj q) 0 := by simpa [hq0] using (embed_proj q).symm
      obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hz
      obtain ⟨u, v, hu, hv, huv, hzopen'⟩ := hzopen
      have pz : embed z 0 ∈ segment ℝ p q := by
        refine ⟨α, β, hα, hβ, hαβ, ?_⟩
        calc
          α • p + β • q = α • embed (proj p) 0 + β • embed (proj q) 0 := by
            rw [congrArg (fun x => α • x) hp_id,
              congrArg (fun x => β • x) hq_id]
          _ = embed (α • proj p + β • proj q) (α * 0 + β * 0) :=
            (embed_affine α β hαβ (proj p) (proj q) 0 0).symm
          _ = embed z 0 := by simp [hzcomb]
      have hopW : embed z 0 ∈ openSegment ℝ (embed r 0) (embed s 0) := by
        refine ⟨u, v, hu, hv, huv, ?_⟩
        calc
          u • embed r 0 + v • embed s 0
              = embed (u • r + v • s) (u * 0 + v * 0) :=
                (embed_affine u v huv r s 0 0).symm
          _ = embed z 0 := by simp [hzopen']
      have hrW : embed r 0 ∈ Hpoly (wedgeA a i0) (wedgeB b) := embed_mem_of_mem a b i0 hr
      have hsW : embed s 0 ∈ Hpoly (wedgeA a i0) (wedgeB b) := embed_mem_of_mem a b i0 hs
      have hr_seg : embed r 0 ∈ segment ℝ p q :=
        hextr.left_mem_of_mem_openSegment hrW hsW pz hopW
      obtain ⟨α', β', hα', hβ', hαβ', hrcomb⟩ := hr_seg
      refine ⟨α', β', hα', hβ', hαβ', ?_⟩
      have : r = α' • proj p + β' • proj q := by
        simpa [proj_embed, proj_add, proj_smul] using congrArg proj hrcomb.symm
      exact this.symm
    | inr htop =>
      have hp_id : p = embed (proj p) (b i0 - ⟪a i0, proj p⟫) := by
        simpa [htop p (left_mem_segment _ _ _)] using (embed_proj p).symm
      have hq_id : q = embed (proj q) (b i0 - ⟪a i0, proj q⟫) := by
        simpa [htop q (right_mem_segment _ _ _)] using (embed_proj q).symm
      obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hz
      obtain ⟨u, v, hu, hv, huv, hzopen'⟩ := hzopen
      have haffz : b i0 - ⟪a i0, α • proj p + β • proj q⟫ =
          α * (b i0 - ⟪a i0, proj p⟫) + β * (b i0 - ⟪a i0, proj q⟫) := by
        simp [inner_add_right, inner_smul_right, mul_sub]
        linarith [weighted_const α β (b i0) hαβ]
      have haffz' : b i0 - ⟪a i0, z⟫ =
          α * (b i0 - ⟪a i0, proj p⟫) + β * (b i0 - ⟪a i0, proj q⟫) := by
        simpa [hzcomb] using haffz
      have pz : embed z (b i0 - ⟪a i0, z⟫) ∈ segment ℝ p q := by
        refine ⟨α, β, hα, hβ, hαβ, ?_⟩
        calc
          α • p + β • q
              = α • embed (proj p) (b i0 - ⟪a i0, proj p⟫) +
                β • embed (proj q) (b i0 - ⟪a i0, proj q⟫) := by
                  rw [congrArg (fun x => α • x) hp_id,
                    congrArg (fun x => β • x) hq_id]
          _ = embed (α • proj p + β • proj q)
                (α * (b i0 - ⟪a i0, proj p⟫) + β * (b i0 - ⟪a i0, proj q⟫)) :=
                (embed_affine α β hαβ (proj p) (proj q)
                  (b i0 - ⟪a i0, proj p⟫) (b i0 - ⟪a i0, proj q⟫)).symm
          _ = embed z (b i0 - ⟪a i0, z⟫) := by rw [hzcomb, haffz']
      have haffopen : b i0 - ⟪a i0, u • r + v • s⟫ =
          u * (b i0 - ⟪a i0, r⟫) + v * (b i0 - ⟪a i0, s⟫) := by
        simp [inner_add_right, inner_smul_right, mul_sub]
        linarith [weighted_const u v (b i0) huv]
      have haffopen' : b i0 - ⟪a i0, z⟫ =
          u * (b i0 - ⟪a i0, r⟫) + v * (b i0 - ⟪a i0, s⟫) := by
        simpa [hzopen'] using haffopen
      have hopW : embed z (b i0 - ⟪a i0, z⟫) ∈
          openSegment ℝ (embed r (b i0 - ⟪a i0, r⟫)) (embed s (b i0 - ⟪a i0, s⟫)) := by
        refine ⟨u, v, hu, hv, huv, ?_⟩
        calc
          u • embed r (b i0 - ⟪a i0, r⟫) + v • embed s (b i0 - ⟪a i0, s⟫)
              = embed (u • r + v • s)
                (u * (b i0 - ⟪a i0, r⟫) + v * (b i0 - ⟪a i0, s⟫)) :=
                (embed_affine u v huv r s (b i0 - ⟪a i0, r⟫) (b i0 - ⟪a i0, s⟫)).symm
          _ = embed z (b i0 - ⟪a i0, z⟫) := by rw [hzopen', haffopen']
      have hrW := embed_mem_upper a b i0 hr
      have hsW := embed_mem_upper a b i0 hs
      have hr_seg : embed r (b i0 - ⟪a i0, r⟫) ∈ segment ℝ p q :=
        hextr.left_mem_of_mem_openSegment hrW hsW pz hopW
      obtain ⟨α', β', hα', hβ', hαβ', hrcomb⟩ := hr_seg
      refine ⟨α', β', hα', hβ', hαβ', ?_⟩
      have : r = α' • proj p + β' • proj q := by
        simpa [proj_embed, proj_add, proj_smul] using congrArg proj hrcomb.symm
      exact this.symm

lemma diamLE_wedge (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i0 : Fin n)
    {L : ℕ} (hW : DiamLE (Hpoly (wedgeA a i0) (wedgeB b)) L) :
    DiamLE (Hpoly a b) L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwL, hs⟩ :=
    hW (embed u 0) (bottom_extreme a b i0 hu) (embed v 0) (bottom_extreme a b i0 hv)
  refine ⟨fun i => proj (w i), ?_, ?_, ?_⟩
  · simp [hw0, proj_embed]
  · simp [hwL, proj_embed]
  · intro i hi
    rcases hs i hi with heq | hadj
    · exact Or.inl (congrArg proj heq)
    · exact proj_adj a b i0 hadj

lemma diamLE_of_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q : Set E}
    (h : P = Q) (B : ℕ) : DiamLE P B ↔ DiamLE Q B := by
  subst h; rfl

end HirschWedge

open HirschWedge

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
      D = d + (n - 2 * d) ∧
      (Hpoly aQ bQ).Nonempty ∧
      Bornology.IsBounded (Hpoly aQ bQ) ∧
      ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L := by
  suffices ∀ (k d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)),
      n - 2 * d = k →
      ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
        D = d + (n - 2 * d) ∧
        (Hpoly aQ bQ).Nonempty ∧
        Bornology.IsBounded (Hpoly aQ bQ) ∧
        ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L by
    exact this (n - 2 * d) d n a b hne hbd rfl
  intro k
  induction k with
  | zero =>
    intro d n a b hne hbd hk
    have hn : n ≤ 2 * d := by omega
    refine ⟨d, padA a, padB b, ?_, ?_, ?_, ?_⟩
    · simp [hk]
    · simpa [hpoly_pad hn a b] using hne
    · simpa [hpoly_pad hn a b] using hbd
    · intro L hL
      exact (diamLE_of_eq (hpoly_pad hn a b) L).1 hL
  | succ k ih =>
    intro d n a b hne hbd hk
    have hn : 2 * d < n := by omega
    have i0 : Fin n := ⟨0, by omega⟩
    have hneW := wedge_nonempty a b i0 hne
    have hbdW := wedge_bounded a b i0 hbd
    have hk' : (n + 1) - 2 * (d + 1) = k := by omega
    obtain ⟨D, aQ, bQ, hD, hneQ, hbdQ, htr⟩ :=
      ih (d + 1) (n + 1) (wedgeA a i0) (wedgeB b) hneW hbdW hk'
    refine ⟨D, aQ, bQ, ?_, hneQ, hbdQ, ?_⟩
    · omega
    · intro L hL
      exact diamLE_wedge a b i0 (htr L hL)
