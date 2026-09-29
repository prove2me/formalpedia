-- Prove2me | solution 2 for QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:52:09.547174+00:00
-- url     : https://prove2.me/submissions/1a78fa8d-326e-4873-bf1f-fee7320c4540

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesDenominatorSharp
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLattices.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, I: the analytic core

Quantizing a transformer's weight tensor means replacing each real entry by the
nearest point of a *modular lattice grid* `δ·ℤ ⊆ ℝ` (in practice: an integer
`INT-k` code times a scale).  This file proves that this operation preserves the
**global convexity invariants** of the loss landscape *quantitatively*:

* the quantized loss `f ∘ Q` is `2Lr`-approximately convex (`quantized_approxConvex`);
* the best lattice weight is within `L·r` of the *global* optimum
  (`quantized_min_gap`), where `r` is the covering radius of the grid;
* under quadratic growth the lattice minimiser is `√(2Lr/μ)`-close to the true
  minimiser (`quantized_minimizer_close`);
* sublevel sets of the quantized loss are sandwiched between two genuinely convex
  sets (`sublevel_sandwich`), so all sublevel-convexity invariants survive up to
  the covering radius;
* **capstone / reverse transfer**: if along a tower of refining lattices the
  quantized landscapes are `εₘ`-approximately convex with `εₘ → 0`, then the
  underlying continuous loss is *exactly* convex (`convexOn_of_approxConvex_tower`).
  Convexity is therefore an invariant certifiable from finite, quantized data.

The arithmetic (modular / CRT / lattice-tower) layer lives in
`Bridges.QuantizedWeightLatticesModular`.
-/

namespace QuantizedWeightLattices

open Set Filter Topology

/-! ## Section 1: the scalar grid quantizer `δ·ℤ` -/

-- [dropped: platform already declares gridRound]
lemma gridRound_mem_zmultiples (δ x : ℝ) :
    gridRound δ x ∈ AddSubgroup.zmultiples δ := by
  refine ⟨round (x / δ), ?_⟩
  simp [gridRound, zsmul_eq_mul, mul_comm]

/-- **Covering radius of the grid**: rounding moves a weight by at most `δ/2`. -/
-- [dropped: platform already declares gridRound_error]
lemma gridRound_eq_self_iff {δ : ℝ} (hδ : δ ≠ 0) (y : ℝ) :
    gridRound δ y = y ↔ y ∈ AddSubgroup.zmultiples δ := by
  constructor
  · intro h; rw [← h]; exact gridRound_mem_zmultiples δ y
  · rintro ⟨k, hk⟩
    have hk' : y = δ * (k : ℝ) := by
      rw [← hk]; simp [zsmul_eq_mul, mul_comm]
    subst hk'
    simp [gridRound, mul_div_cancel_left₀ _ hδ]

/-- Quantization is idempotent: re-quantizing an already quantized weight is a no-op. -/
lemma gridRound_idem {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) :
    gridRound δ (gridRound δ x) = gridRound δ x :=
  (gridRound_eq_self_iff hδ _).2 (gridRound_mem_zmultiples δ x)

/-! ## Section 2: quantizing a whole weight tensor

A transformer weight tensor is a function `ι → ℝ` for a finite index type `ι`
(e.g. `ι = Fin dout × Fin din` for one matrix, or a sigma type over all layers).
`ι → ℝ` carries the sup norm, the natural norm for entrywise quantization. -/

section Tensor

variable {ι : Type*} [Fintype ι]

-- [dropped: platform already declares quantizeTensor]
lemma quantizeTensor_mem_lattice (δ : ℝ) (W : ι → ℝ) (i : ι) :
    quantizeTensor δ W i ∈ AddSubgroup.zmultiples δ :=
  gridRound_mem_zmultiples δ (W i)

/-- **Uniform quantization error**: the tensor moves by at most `δ/2` in sup norm. -/
-- [dropped: platform already declares quantizeTensor_error]
lemma quantizeTensor_idem {δ : ℝ} (hδ : δ ≠ 0) (W : ι → ℝ) :
    quantizeTensor δ (quantizeTensor δ W) = quantizeTensor δ W := by
  funext i; exact gridRound_idem hδ (W i)

end Tensor

/-! ## Section 3: abstract quantizers -/

-- [dropped: platform already declares Quantizer]
-- [dropped: platform already declares gridQuantizer]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- [dropped: platform already declares ApproxConvexOn]
lemma ApproxConvexOn.mono {ε ε' : ℝ} {s : Set E} {g : E → ℝ}
    (h : ApproxConvexOn ε s g) (hle : ε ≤ ε') : ApproxConvexOn ε' s g := by
  intro x hx y hy a b ha hb hab
  exact (h hx hy ha hb hab).trans (by linarith)

/-- Exact convexity is the `ε = 0` case. -/
lemma ConvexOn.approxConvexOn {s : Set E} {g : E → ℝ} (h : ConvexOn ℝ s g) :
    ApproxConvexOn 0 s g := by
  intro x hx y hy a b ha hb hab
  simpa using h.2 hx hy ha hb hab

/-- Conversely, a `0`-approximately convex function on a convex set is convex. -/
lemma ApproxConvexOn.convexOn_of_zero {s : Set E} {g : E → ℝ} (hs : Convex ℝ s)
    (h : ApproxConvexOn 0 s g) : ConvexOn ℝ s g :=
  ⟨hs, fun _ hx _ hy _ _ ha hb hab => by simpa using h hx hy ha hb hab⟩

/-! ## Section 5: transfer of convexity through quantization -/

section Transfer

variable {L : NNReal} {f : E → ℝ}

omit [NormedSpace ℝ E] in
lemma abs_sub_le_lipschitz (hL : LipschitzWith L f) (x y : E) :
    |f x - f y| ≤ (L : ℝ) * ‖x - y‖ := by
  have h := hL.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at h

omit [NormedSpace ℝ E] in
/-- Quantizing a weight can increase the loss by at most `L·r`. -/
lemma loss_quantize_le (hL : LipschitzWith L f) (Q : Quantizer E) (x : E) :
    f (Q.toFun x) ≤ f x + (L : ℝ) * Q.radius := by
  have h1 : |f (Q.toFun x) - f x| ≤ (L : ℝ) * ‖Q.toFun x - x‖ := abs_sub_le_lipschitz hL _ _
  have h2 : (L : ℝ) * ‖Q.toFun x - x‖ ≤ (L : ℝ) * Q.radius :=
    mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg
  have h3 := (abs_le.1 (h1.trans h2)).2
  linarith

omit [NormedSpace ℝ E] in
/-- ... and can decrease it by at most `L·r`. -/
lemma loss_le_quantize (hL : LipschitzWith L f) (Q : Quantizer E) (x : E) :
    f x ≤ f (Q.toFun x) + (L : ℝ) * Q.radius := by
  have h1 : |f (Q.toFun x) - f x| ≤ (L : ℝ) * ‖Q.toFun x - x‖ := abs_sub_le_lipschitz hL _ _
  have h2 : (L : ℝ) * ‖Q.toFun x - x‖ ≤ (L : ℝ) * Q.radius :=
    mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg
  have h3 := (abs_le.1 (h1.trans h2)).1
  linarith

/-- **Theorem A (convexity is preserved up to the covering radius).**
If the continuous loss `f` is convex and `L`-Lipschitz, the quantized loss
`f ∘ Q` obtained by projecting weights onto the lattice is `2·L·r`-approximately
convex, where `r` is the covering radius.  For the `δ`-grid this defect is `L·δ`. -/
theorem quantized_approxConvex (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    (Q : Quantizer E) : ApproxConvexOn (2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by
  intro x _ y _ a b ha hb hab
  have hmid : f (Q.toFun (a • x + b • y)) ≤ f (a • x + b • y) + (L : ℝ) * Q.radius :=
    loss_quantize_le hL Q _
  have hconv : f (a • x + b • y) ≤ a * f x + b * f y :=
    hf.2 (mem_univ x) (mem_univ y) ha hb hab
  have hx : f x ≤ f (Q.toFun x) + (L : ℝ) * Q.radius := loss_le_quantize hL Q x
  have hy : f y ≤ f (Q.toFun y) + (L : ℝ) * Q.radius := loss_le_quantize hL Q y
  have hax : a * f x ≤ a * (f (Q.toFun x) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left hx ha
  have hby : b * f y ≤ b * (f (Q.toFun y) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left hy hb
  have hab' : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius) = (L : ℝ) * Q.radius := by
    have : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius)
        = (a + b) * ((L : ℝ) * Q.radius) := by ring
    rw [this, hab, one_mul]
  simp only [Function.comp_apply]
  nlinarith [hmid, hconv, hax, hby, hab']

omit [NormedSpace ℝ E] in
/-- **Theorem B (no global optimum is lost).**  If `x₀` is a global minimiser of an
`L`-Lipschitz loss, then the *lattice point* `Q x₀` is an `L·r`-approximate global
minimiser: no real weight configuration beats it by more than `L·r`. -/
theorem quantized_optimum_gap (hL : LipschitzWith L f) (Q : Quantizer E) {x₀ : E}
    (hmin : ∀ x, f x₀ ≤ f x) (x : E) : f (Q.toFun x₀) ≤ f x + (L : ℝ) * Q.radius :=
  (loss_quantize_le hL Q x₀).trans (by linarith [hmin x])

omit [NormedSpace ℝ E] in
/-- **Theorem C (minimiser localisation).**  If the loss has quadratic growth of
modulus `μ > 0` around its minimiser `x₀` (the standard consequence of strong
convexity) then *any* loss-minimising lattice point `ŵ` lies within
`√(2Lr/μ)` of `x₀`: quantization cannot relocate the basin of attraction. -/
theorem quantized_minimizer_close {μ : ℝ} (hμ : 0 < μ) {x₀ ŵ : E}
    (hL : LipschitzWith L f) (Q : Quantizer E)
    (hgrowth : ∀ x, μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀)
    (hlat : ∀ x, f ŵ ≤ f (Q.toFun x)) :
    ‖ŵ - x₀‖ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) := by
  have h1 : f ŵ ≤ f (Q.toFun x₀) := hlat x₀
  have h2 : f (Q.toFun x₀) ≤ f x₀ + (L : ℝ) * Q.radius := loss_quantize_le hL Q x₀
  have h3 : μ / 2 * ‖ŵ - x₀‖ ^ 2 ≤ f ŵ - f x₀ := hgrowth ŵ
  have h4 : μ / 2 * ‖ŵ - x₀‖ ^ 2 ≤ (L : ℝ) * Q.radius := by linarith
  have h5 : ‖ŵ - x₀‖ ^ 2 ≤ 2 * (L : ℝ) * Q.radius / μ := by
    rw [le_div_iff₀ hμ]; nlinarith
  calc ‖ŵ - x₀‖ = Real.sqrt (‖ŵ - x₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) := Real.sqrt_le_sqrt h5

/-- **Theorem D (sublevel sandwich).**  The sublevel sets of the quantized loss are
trapped between two *convex* sublevel sets of the continuous loss, at distance
`L·r` in level.  Hence every convexity invariant of the landscape's sublevel
filtration (connectedness, star-shapedness, contractibility of level sets, …) is
preserved up to a level shift of `L·r`. -/
theorem sublevel_sandwich (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    (Q : Quantizer E) (c : ℝ) :
    Convex ℝ {x : E | f x ≤ c - (L : ℝ) * Q.radius} ∧
      {x : E | f x ≤ c - (L : ℝ) * Q.radius} ⊆ {x : E | f (Q.toFun x) ≤ c} ∧
      {x : E | f (Q.toFun x) ≤ c} ⊆ {x : E | f x ≤ c + (L : ℝ) * Q.radius} ∧
      Convex ℝ {x : E | f x ≤ c + (L : ℝ) * Q.radius} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hf.convex_le (c - (L : ℝ) * Q.radius)
  · intro x hx
    have := loss_quantize_le hL Q x
    simp only [mem_setOf_eq] at hx ⊢
    linarith
  · intro x hx
    have := loss_le_quantize hL Q x
    simp only [mem_setOf_eq] at hx ⊢
    linarith
  · simpa using hf.convex_le (c + (L : ℝ) * Q.radius)

end Transfer

/-! ## Section 6: the capstone — exact convexity from the lattice tower -/

/-- **Theorem E (reverse transfer / projective limit of the lattice tower).**
Let `f` be an `L`-Lipschitz loss and let `Qₘ` be a tower of quantizers whose
covering radii tend to `0` (e.g. the grids `δ/m·ℤ` along a divisibility tower).
If each quantized landscape `f ∘ Qₘ` is `εₘ`-approximately convex with `εₘ → 0`,
then the *continuous* loss is exactly convex.

This is the converse direction of Theorem A: global convexity of the real-valued
landscape is an invariant that can be certified purely from finitely-supported
quantized measurements. -/
theorem convexOn_of_approxConvex_tower {L : NNReal} {f : E → ℝ} (hL : LipschitzWith L f)
    (Q : ℕ → Quantizer E) (eps : ℕ → ℝ)
    (hr : Tendsto (fun m => (Q m).radius) atTop (𝓝 0))
    (heps : Tendsto eps atTop (𝓝 0))
    (hac : ∀ m, ApproxConvexOn (eps m) univ (f ∘ (Q m).toFun)) :
    ConvexOn ℝ univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  -- the defect sequence
  set A : ℝ := a * f x + b * f y with hA
  have key : ∀ m, f (a • x + b • y) ≤ A + (eps m + 2 * (L : ℝ) * (Q m).radius) := by
    intro m
    have h0 := hac m (mem_univ x) (mem_univ y) ha hb hab
    simp only [Function.comp_apply] at h0
    have hmid : f (a • x + b • y) ≤ f ((Q m).toFun (a • x + b • y)) + (L : ℝ) * (Q m).radius :=
      loss_le_quantize hL (Q m) _
    have hx : f ((Q m).toFun x) ≤ f x + (L : ℝ) * (Q m).radius := loss_quantize_le hL (Q m) x
    have hy : f ((Q m).toFun y) ≤ f y + (L : ℝ) * (Q m).radius := loss_quantize_le hL (Q m) y
    have hax : a * f ((Q m).toFun x) ≤ a * (f x + (L : ℝ) * (Q m).radius) :=
      mul_le_mul_of_nonneg_left hx ha
    have hby : b * f ((Q m).toFun y) ≤ b * (f y + (L : ℝ) * (Q m).radius) :=
      mul_le_mul_of_nonneg_left hy hb
    have hsum : a * ((L : ℝ) * (Q m).radius) + b * ((L : ℝ) * (Q m).radius)
        = (L : ℝ) * (Q m).radius := by
      have : a * ((L : ℝ) * (Q m).radius) + b * ((L : ℝ) * (Q m).radius)
          = (a + b) * ((L : ℝ) * (Q m).radius) := by ring
      rw [this, hab, one_mul]
    rw [hA]
    nlinarith [hmid, h0, hax, hby, hsum]
  have hlim : Tendsto (fun m => A + (eps m + 2 * (L : ℝ) * (Q m).radius)) atTop (𝓝 A) := by
    have h1 : Tendsto (fun m => eps m + 2 * (L : ℝ) * (Q m).radius) atTop (𝓝 0) := by
      simpa using heps.add ((hr.const_mul (2 * (L : ℝ))).congr (fun m => by ring))
    simpa using (tendsto_const_nhds (x := A) (f := atTop (α := ℕ))).add h1
  exact ge_of_tendsto hlim (Eventually.of_forall key)

/-! ## Section 7: the concrete grid tower -/

section GridTower

variable {ι : Type*} [Fintype ι]

/-- Refining the grid: for `m ∣ m'` (both positive) the coarse lattice `(δ/m)·ℤ`
is contained in the fine lattice `(δ/m')·ℤ`.  This is the divisibility tower of
quantization grids. -/
theorem zmultiples_mono_of_dvd {δ : ℝ} {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hdvd : m ∣ m') :
    AddSubgroup.zmultiples (δ / m) ≤ AddSubgroup.zmultiples (δ / m') := by
  obtain ⟨c, rfl⟩ := hdvd
  have hc : (c : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h] at hm'
    · exact Nat.cast_ne_zero.2 h.ne'
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  rintro _ ⟨k, rfl⟩
  refine ⟨k * c, ?_⟩
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp

/-- The covering radius of the `m`-th grid in the tower `δ/(m+1)` tends to `0`. -/
theorem gridTower_radius_tendsto_zero (δ : ℝ) :
    Tendsto (fun m : ℕ => δ / (m + 1) / 2) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => δ / (m + 1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  simpa using h.div_const 2

/-- The tower of grid quantizers on a weight tensor space, `Qₘ` with mesh `δ/(m+1)`. -/
-- [dropped: platform already declares gridTower]
lemma gridTower_radius (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    (gridTower (ι := ι) δ hδ m).radius = δ / (m + 1) / 2 := rfl

/-- **Corollary (tower version of Theorem A).**  Along the refining tower the
convexity defect of the quantized transformer landscape is `L·δ/(m+1)` and hence
tends to zero: the quantized loss landscapes converge to a convex landscape. -/
theorem gridTower_defect_tendsto_zero {L : NNReal} (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m : ℕ => 2 * (L : ℝ) * (gridTower (ι := ι) δ hδ m).radius) atTop (𝓝 0) := by
  simpa using ((gridTower_radius_tendsto_zero δ).const_mul (2 * (L : ℝ)))

/-- **Corollary (Theorem E on the concrete grid tower).**  If for every mesh
`δ/(m+1)` the entrywise-quantized transformer loss is `εₘ`-approximately convex
with `εₘ → 0`, then the continuous loss is convex. -/
theorem convexOn_of_grid_approxConvex {L : NNReal} {f : (ι → ℝ) → ℝ} (hL : LipschitzWith L f)
    {δ : ℝ} (hδ : 0 < δ) (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0))
    (hac : ∀ m : ℕ, ApproxConvexOn (eps m) univ (f ∘ quantizeTensor (δ / (m + 1)))) :
    ConvexOn ℝ univ f := by
  refine convexOn_of_approxConvex_tower hL (gridTower (ι := ι) δ hδ) eps ?_ heps ?_
  · simpa [gridTower_radius] using gridTower_radius_tendsto_zero δ
  · intro m; exact hac m

end GridTower

end QuantizedWeightLattices
-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLatticesModular.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, II: the modular layer

The analytic core (`Bridges.QuantizedWeightLattices`) shows that projecting weights
onto the grid `δ·ℤ` perturbs the loss landscape's convexity invariants by at most
`2·L·r`, `r` the covering radius.  Here we identify the *arithmetic* object that
indexes the quantization codebook.

Main results.

* `codeHom_injective` — the `m`-symbol codebook `ZMod m` embeds into the weight
  torus `AddCircle δ = ℝ / δℤ` as the subgroup generated by `δ/m`.
* `range_codeHom` — its image is **exactly the `m`-torsion** of the weight torus:
  quantization codes are arithmetic (torsion) points, not arbitrary reals.
* `nat_card_torsion` — hence the torus carries exactly `m` codes at precision `m`.
* `codebook_card` — a weight tensor codebook has `m ^ |ι|` elements.
* `codebook_crt` / `codebook_card_crt` — coprime **mixed precision splits by CRT**:
  `ZMod (m*n) ≃+ ZMod m × ZMod n`, i.e. a `mn`-level quantizer factors as
  independent `m`- and `n`-level quantizers.
* `torsion_mono_of_dvd` — the divisibility tower of codebooks is a tower of
  subgroups of the weight torus.
* `bitwidth_defect` — a `b`-bit quantizer of a convex `L`-Lipschitz loss yields a
  landscape that is `L·δ/2^b`-approximately convex, and
  `bitwidth_defect_halves` — each extra bit halves the convexity defect while the
  codebook doubles: `defect(b) · 2^b = L·δ` is a conserved scaling law.
-/

namespace QuantizedWeightLattices.Modular

open QuantizedWeightLattices Set

/-! ## Section 1: the codebook homomorphism `ZMod m → ℝ/δℤ` -/

section Codebook

variable (δ : ℝ) (m : ℕ)

-- [dropped: platform already declares codeHomInt]
-- [dropped: platform already declares codeHomInt_apply]
-- [dropped: platform already declares codeHomInt_period]
-- [dropped: platform already declares codeHom]
lemma codeHom_intCast (hm : 0 < m) (k : ℤ) :
    codeHom δ m hm (k : ZMod m) = ((k • (δ / m) : ℝ) : AddCircle δ) := by
  rw [codeHom, ZMod.lift_coe]
  rfl

/-- **Theorem M1 (faithfulness of the codebook).**  Distinct codes name distinct
points of the weight torus: no precision is wasted. -/
theorem codeHom_injective (hδ : 0 < δ) (hm : 0 < m) :
    Function.Injective (codeHom δ m hm) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [codeHom_intCast] at hx
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff δ).1 hx
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hk : (k : ℝ) = (n : ℝ) * m := by
    have h1 : (n : ℝ) * δ = (k : ℝ) * (δ / m) := by
      simpa [zsmul_eq_mul] using hn
    field_simp at h1
    nlinarith [h1, hδ]
  have hkz : k = n * m := by exact_mod_cast hk
  rw [hkz]
  simp

/-- **Theorem M2 (codes are torsion points).**  The image of the `m`-symbol
codebook inside the weight torus `ℝ/δℤ` is *exactly* the `m`-torsion subgroup.
Quantized weights are arithmetic points of the torus; the codebook is not merely
contained in the torsion, it exhausts it. -/
theorem range_codeHom (hm : 0 < m) :
    Set.range (codeHom δ m hm) = {x : AddCircle δ | (m : ℕ) • x = 0} := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  ext x
  simp only [mem_range, mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (m : ℕ) • y = 0 := by
      rw [nsmul_eq_mul]; simp
    rw [← map_nsmul, hy, map_zero]
  · intro hx
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples δ) x
    have h1 : ((m • t : ℝ) : AddCircle δ) = 0 := by
      rw [AddCircle.coe_nsmul]
      exact hx
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff δ).1 h1
    refine ⟨((n : ℤ) : ZMod m), ?_⟩
    rw [codeHom_intCast]
    have ht : t = (n : ℝ) * (δ / m) := by
      have h2 : (n : ℝ) * δ = (m : ℝ) * t := by
        simpa [zsmul_eq_mul, nsmul_eq_mul] using hn
      field_simp
      linarith [h2]
    rw [ht]
    simp [zsmul_eq_mul]

/-- **Theorem M3 (size of the codebook = order of the torsion group).**  The weight
torus `ℝ/δℤ` has exactly `m` points of order dividing `m`, so an `m`-level
quantizer is *exactly* as expressive as the arithmetic of `ZMod m`. -/
theorem nat_card_torsion (hδ : 0 < δ) (hm : 0 < m) :
    Nat.card {x : AddCircle δ | (m : ℕ) • x = 0} = m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hbij : Nat.card (Set.range (codeHom δ m hm)) = Nat.card (ZMod m) :=
    Nat.card_congr (Equiv.ofInjective _ (codeHom_injective δ m hδ hm)).symm
  rw [range_codeHom δ m hm] at hbij
  rw [hbij, Nat.card_eq_fintype_card, ZMod.card]

/-- The order of the generating quantization step `δ/m` in the weight torus is `m`. -/
theorem addOrderOf_step (hδ : 0 < δ) (hm : 0 < m) :
    addOrderOf ((δ / m : ℝ) : AddCircle δ) = m := by
  haveI : Fact (0 < δ) := ⟨hδ⟩
  exact AddCircle.addOrderOf_period_div hm

end Codebook

/-! ## Section 2: tensor codebooks, CRT mixed precision, and the divisibility tower -/

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem M4 (codebook size of a weight tensor).**  Quantizing every entry of a
weight tensor indexed by `ι` at precision `m` gives exactly `m ^ |ι|` codes. -/
theorem codebook_card (m : ℕ) [NeZero m] :
    Fintype.card (ι → ZMod m) = m ^ Fintype.card ι := by
  simp [ZMod.card]

/-- **Theorem M5 (CRT mixed precision).**  For coprime precisions the codebook of a
`m·n`-level quantizer splits canonically as a product of an `m`-level and an
`n`-level codebook — a Chinese-Remainder decomposition of quantized weight space. -/
-- [dropped: platform already declares codebook_crt]
theorem codebook_card_crt {m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    Fintype.card (ι → ZMod (m * n)) =
      Fintype.card (ι → ZMod m) * Fintype.card (ι → ZMod n) := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [Fintype.card_congr (codebook_crt (ι := ι) h).toEquiv, Fintype.card_prod]

/-- **Theorem M6 (the divisibility tower of codebooks).**  If `m ∣ m'` then every
`m`-level code is an `m'`-level code: refining precision along a divisibility
tower gives an increasing tower of torsion subgroups of the weight torus. -/
theorem torsion_mono_of_dvd (δ : ℝ) {m m' : ℕ} (hdvd : m ∣ m') :
    {x : AddCircle δ | (m : ℕ) • x = 0} ⊆ {x : AddCircle δ | (m' : ℕ) • x = 0} := by
  obtain ⟨c, rfl⟩ := hdvd
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  have h : (m * c) • x = c • (m • x) := by rw [mul_nsmul, smul_comm]
  rw [h, hx, smul_zero]

end Tensor

/-! ## Section 3: bit width versus convexity defect -/

section BitWidth

variable {ι : Type*} [Fintype ι] {L : NNReal} {f : (ι → ℝ) → ℝ}

/-- **Theorem M7 (`b`-bit quantization of a convex landscape).**  Quantizing a convex
`L`-Lipschitz loss with a `b`-bit uniform quantizer of dynamic range `δ` produces a
landscape that is `L·δ/2^b`-approximately convex. -/
theorem bitwidth_defect (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    {δ : ℝ} (hδ : 0 < δ) (b : ℕ) :
    ApproxConvexOn ((L : ℝ) * δ / 2 ^ b) univ (f ∘ quantizeTensor (δ / 2 ^ b)) := by
  have hpos : (0 : ℝ) < δ / 2 ^ b := by positivity
  have h := quantized_approxConvex hf hL (gridQuantizer (ι := ι) hpos)
  have hrad : 2 * (L : ℝ) * (gridQuantizer (ι := ι) hpos).radius = (L : ℝ) * δ / 2 ^ b := by
    show 2 * (L : ℝ) * ((δ / 2 ^ b) / 2) = (L : ℝ) * δ / 2 ^ b
    ring
  rw [hrad] at h
  exact h

/-- **Theorem M8 (conserved scaling law).**  Each additional bit halves the convexity
defect while doubling the codebook: the product `defect(b) · 2^b` is the constant
`L·δ`, independent of the bit width. -/
theorem bitwidth_defect_halves {δ : ℝ} (b : ℕ) :
    (L : ℝ) * δ / 2 ^ (b + 1) = ((L : ℝ) * δ / 2 ^ b) / 2 ∧
      ((L : ℝ) * δ / 2 ^ b) * 2 ^ b = (L : ℝ) * δ := by
  have h2 : (2 : ℝ) ^ b ≠ 0 := by positivity
  constructor
  · rw [pow_succ]
    field_simp
  · field_simp

end BitWidth

end QuantizedWeightLattices.Modular
-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLatticesSharp.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, III: sharpness and density

Adversarial (Stage 4) companion to the two previous files.  Two questions are
answered here.

**Is the convexity-preservation theorem vacuous?**  No.  For the archetypal convex
`1`-Lipschitz loss `x ↦ |x|` the `δ`-grid quantized landscape is *provably not
convex*: its convexity defect is at least `δ/2` (`quantized_abs_defect_ge`), while
Theorem A bounds it by `δ`.  Hence the constant `2·L·r` of Theorem A is sharp up
to a factor of two (`defect_bound_sharp`), and the phrase "convexity is preserved"
must be read in the quantitative, approximate sense — exact convexity really is
destroyed (`quantized_abs_not_convex`).  Moreover, over the *whole* class of
radius-`r` quantizers the constant `2·L·r` is exactly optimal
(`abstract_defect_bound_optimal`): the residual factor-two question concerns only
nearest-point projections.

**How rich is the arithmetic of the codebook tower?**  The `m`-level codebooks are
the torsion subgroups of the weight torus `ℝ/δℤ`; they form a divisibility tower
with index `m'/m` (`torsion_card_ratio`) whose union — the full torsion subgroup,
an avatar of `ℚ/ℤ` — is **dense** in the weight torus
(`dense_quantization_tower`).  This is the arithmetic mechanism behind the reverse
transfer theorem (Theorem E): the tower of finite codebooks sees all of weight
space in the limit.
-/

namespace QuantizedWeightLattices.Sharp

open QuantizedWeightLattices QuantizedWeightLattices.Modular Set

/-! ## Section 1: the scalar quantizer and the model loss `|·|` -/

-- [dropped: platform already declares scalarQuantizer]
lemma convexOn_abs_real : ConvexOn ℝ univ (fun x : ℝ => |x|) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc |a • x + b • y| ≤ |a • x| + |b • y| := abs_add_le _ _
    _ = a * |x| + b * |y| := by
        simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

lemma lipschitzWith_abs_real : LipschitzWith 1 (fun x : ℝ => |x|) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

/-! ## Section 2: three explicit rounding computations -/

lemma gridRound_two_fifths {δ : ℝ} (hδ : 0 < δ) : gridRound δ (2 * δ / 5) = 0 := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : 2 * δ / 5 / δ = 2 / 5 := by field_simp
  have hr : round ((2 : ℝ) / 5) = 0 := by
    rw [round_eq]
    norm_num
  simp [gridRound, hx, hr]

lemma gridRound_three_fifths {δ : ℝ} (hδ : 0 < δ) : gridRound δ (3 * δ / 5) = δ := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : 3 * δ / 5 / δ = 3 / 5 := by field_simp
  have hr : round ((3 : ℝ) / 5) = 1 := by
    rw [round_eq]
    norm_num
  simp [gridRound, hx, hr]

lemma gridRound_half {δ : ℝ} (hδ : 0 < δ) : gridRound δ (δ / 2) = δ := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : δ / 2 / δ = 1 / 2 := by field_simp
  simp [gridRound, hx]

/-! ## Section 3: the convexity defect of a quantized convex loss is genuinely positive -/

/-- **Theorem S1 (defect lower bound).**  For the convex `1`-Lipschitz loss `|·|`,
any approximate-convexity certificate for the `δ`-grid quantized landscape must
have defect at least `δ/2`.  The witnesses are the weights `2δ/5` and `3δ/5`,
which quantize to `0` and `δ` while their midpoint `δ/2` quantizes *upwards* to
`δ`: rounding creates a genuine bump of height `δ/2`. -/
theorem quantized_abs_defect_ge {δ ε : ℝ} (hδ : 0 < δ)
    (h : ApproxConvexOn ε univ (fun x : ℝ => |gridRound δ x|)) : δ / 2 ≤ ε := by
  have hmid : ((1 : ℝ) / 2) • (2 * δ / 5) + ((1 : ℝ) / 2) • (3 * δ / 5) = δ / 2 := by
    simp only [smul_eq_mul]; ring
  have key := h (mem_univ (2 * δ / 5)) (mem_univ (3 * δ / 5))
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  rw [hmid] at key
  simp only [gridRound_half hδ, gridRound_two_fifths hδ, gridRound_three_fifths hδ,
    abs_of_pos hδ, abs_zero] at key
  linarith

/-- **Theorem S2 (quantization destroys exact convexity).**  The `δ`-grid quantized
version of the convex loss `|·|` is not convex for any positive mesh. -/
theorem quantized_abs_not_convex {δ : ℝ} (hδ : 0 < δ) :
    ¬ ConvexOn ℝ univ (fun x : ℝ => |gridRound δ x|) := by
  intro hconv
  have := quantized_abs_defect_ge hδ hconv.approxConvexOn
  linarith

/-- **Theorem S3 (sharpness of Theorem A up to a factor 2).**  For the loss `|·|`
and mesh `δ` the true convexity defect lies in `[δ/2, δ]`: the general bound
`2·L·r = δ` of `quantized_approxConvex` cannot be improved by more than a factor
of two. -/
theorem defect_bound_sharp {δ : ℝ} (hδ : 0 < δ) :
    ApproxConvexOn δ univ ((fun x : ℝ => |x|) ∘ (scalarQuantizer hδ).toFun) ∧
      ∀ ε : ℝ, ApproxConvexOn ε univ (fun x : ℝ => |gridRound δ x|) → δ / 2 ≤ ε := by
  refine ⟨?_, fun ε hε => quantized_abs_defect_ge hδ hε⟩
  have h := quantized_approxConvex convexOn_abs_real lipschitzWith_abs_real (scalarQuantizer hδ)
  have hrad : 2 * ((1 : NNReal) : ℝ) * (scalarQuantizer hδ).radius = δ := by
    show 2 * ((1 : NNReal) : ℝ) * (δ / 2) = δ
    push_cast
    ring
  rwa [hrad] at h

/-! ## Section 3b: for general quantizers the constant `2·L·r` is exactly optimal -/

/-- A quantizer of radius `r` that displaces every weight by exactly `r`, moving the
sample points `3r, 5r` *inwards* but their midpoint `4r` *outwards*.  It is a
legitimate `Quantizer` (its displacement never exceeds the radius) but it is not a
nearest-point lattice projection. -/
-- [dropped: platform already declares skewQuantizer]
theorem abstract_defect_bound_optimal {r ε : ℝ} (hr : 0 < r)
    (h : ApproxConvexOn ε univ ((fun x : ℝ => |x|) ∘ (skewQuantizer hr).toFun)) :
    2 * r ≤ ε := by
  have h3 : (3 : ℝ) * r ≠ 4 * r := by intro hc; nlinarith
  have h5 : (5 : ℝ) * r ≠ 4 * r := by intro hc; nlinarith
  have e3 : (skewQuantizer hr).toFun (3 * r) = 2 * r := by
    show (if (3 * r : ℝ) = 4 * r then 5 * r else 3 * r - r) = 2 * r
    rw [if_neg h3]; ring
  have e5 : (skewQuantizer hr).toFun (5 * r) = 4 * r := by
    show (if (5 * r : ℝ) = 4 * r then 5 * r else 5 * r - r) = 4 * r
    rw [if_neg h5]; ring
  have e4 : (skewQuantizer hr).toFun (4 * r) = 5 * r := by
    show (if (4 * r : ℝ) = 4 * r then 5 * r else 4 * r - r) = 5 * r
    rw [if_pos rfl]
  have hmid : ((1 : ℝ) / 2) • (3 * r) + ((1 : ℝ) / 2) • (5 * r) = 4 * r := by
    simp only [smul_eq_mul]; ring
  have key := h (mem_univ (3 * r)) (mem_univ (5 * r))
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  rw [hmid] at key
  simp only [Function.comp_apply, e3, e4, e5] at key
  rw [abs_of_pos (by linarith : (0:ℝ) < 5 * r), abs_of_pos (by linarith : (0:ℝ) < 2 * r),
      abs_of_pos (by linarith : (0:ℝ) < 4 * r)] at key
  linarith

/-! ## Section 4: the arithmetic tower of codebooks is dense in the weight torus -/

section Tower

variable (δ : ℝ)

/-- The union of all finite codebooks is exactly the torsion subgroup of the
weight torus `ℝ/δℤ`. -/
theorem torsion_eq_iUnion_codebooks :
    ((AddCommGroup.torsion (AddCircle δ) : AddSubgroup (AddCircle δ)) : Set (AddCircle δ))
      = ⋃ m : {m : ℕ // 0 < m}, {x : AddCircle δ | (m : ℕ) • x = 0} := by
  ext x
  simp only [SetLike.mem_coe, AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero,
    mem_iUnion, mem_setOf_eq, Subtype.exists]
  constructor
  · rintro ⟨n, hn, hx⟩; exact ⟨n, hn, hx⟩
  · rintro ⟨n, hn, hx⟩; exact ⟨n, hn, hx⟩

/-- **Theorem S4 (arithmetic index of the refinement tower).**  Refining the
precision from `m` to a multiple `m'` multiplies the codebook size by exactly the
index `m'/m` of the corresponding torsion subgroups. -/
theorem torsion_card_ratio (hδ : 0 < δ) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hdvd : m ∣ m') :
    Nat.card {x : AddCircle δ | (m' : ℕ) • x = 0}
      = (m' / m) * Nat.card {x : AddCircle δ | (m : ℕ) • x = 0} := by
  rw [nat_card_torsion δ m hδ hm, nat_card_torsion δ m' hδ hm']
  exact (Nat.div_mul_cancel hdvd).symm

/-- **Theorem S5 (density of the quantization tower).**  The union of all finite
codebooks is dense in the weight torus `ℝ/δℤ`.  Equivalently: every real weight is
approximated arbitrarily well by codes of sufficiently high precision — the
arithmetic reason why the approximate-convexity defects of the tower can be driven
to zero (Theorem E). -/
theorem dense_quantization_tower (hδ : 0 < δ) :
    Dense (⋃ m : {m : ℕ // 0 < m}, {x : AddCircle δ | (m : ℕ) • x = 0}) := by
  haveI : Fact (0 < δ) := ⟨hδ⟩
  rw [← torsion_eq_iUnion_codebooks δ, AddCircle.dense_addSubgroup_iff_ne_zmultiples]
  intro a ha hEq
  set n := addOrderOf a with hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero ha
  -- the cyclic group generated by `a` is finite of size `n`
  have hcard : Nat.card (AddSubgroup.zmultiples a) = n := Nat.card_zmultiples a
  haveI hfin' : Finite ↥(AddSubgroup.zmultiples a) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hnpos.ne')
  have hfin : ((AddSubgroup.zmultiples a : AddSubgroup (AddCircle δ)) :
      Set (AddCircle δ)).Finite := Set.toFinite _
  -- but the `(n+1)`-torsion already has `n+1` elements and sits inside it
  have hsub : {x : AddCircle δ | (n + 1 : ℕ) • x = 0} ⊆
      ((AddSubgroup.zmultiples a : AddSubgroup (AddCircle δ)) : Set (AddCircle δ)) := by
    intro x hx
    have hxtor : x ∈ AddCommGroup.torsion (AddCircle δ) := by
      rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero]
      exact ⟨n + 1, Nat.succ_pos n, hx⟩
    rw [hEq] at hxtor
    exact hxtor
  have hcard' : Nat.card {x : AddCircle δ | (n + 1 : ℕ) • x = 0} = n + 1 :=
    nat_card_torsion δ (n + 1) hδ (Nat.succ_pos n)
  have h1 : ({x : AddCircle δ | (n + 1 : ℕ) • x = 0}).ncard ≤
      ((AddSubgroup.zmultiples a : AddSubgroup (AddCircle δ)) : Set (AddCircle δ)).ncard :=
    Set.ncard_le_ncard hsub hfin
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard'] at h1
  simp only [SetLike.coe_sort_coe, hcard] at h1
  omega
end Tower

end QuantizedWeightLattices.Sharp
-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLatticesLandscape.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, IV: landscape invariants

Third cycle of the research loop.  Having established that grid quantization
perturbs convexity by at most `2·L·r` (file I), that the codebook is the torsion
of the weight torus (file II) and that the bound is sharp within a factor two
(file III), we now show that the *finer* invariants of the loss landscape also
survive quantization.

* `quadratic_growth_of_strongConvexOn` — strong convexity forces quadratic growth
  around a global minimiser (proved by an explicit limiting argument along
  `t = 1/(n+1)`).
* `strongConvex_quantized_minimizer_close` — consequently, for a strongly convex
  loss *every* lattice-optimal weight lies within `√(2Lr/μ)` of the true optimum.
* `quantized_approxStrongConvex` — the whole strong-convexity modulus `μ` is
  transported to the quantized landscape, with the same additive defect `2Lr`;
  in particular the curvature invariant `μ` itself is preserved exactly.
* `lattice_infimum_close` — the optimal value of the lattice-restricted problem
  and of the continuous problem differ by at most `L·r`.
-/

namespace QuantizedWeightLattices.Landscape

open QuantizedWeightLattices Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Section 1: strong convexity gives quadratic growth at the optimum -/

/-- **Theorem L1.**  If `f` is `μ`-strongly convex and attains its global minimum at
`x₀`, then it grows at least quadratically away from `x₀`.  The proof takes the
strong-convexity inequality along the segment `t • x + (1-t) • x₀` and lets
`t = 1/(n+1) → 0`. -/
theorem quadratic_growth_of_strongConvexOn {μ : ℝ} {f : E → ℝ} {x₀ : E}
    (hf : StrongConvexOn univ μ f) (hmin : ∀ x, f x₀ ≤ f x) (x : E) :
    μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀ := by
  set C : ℝ := μ / 2 * ‖x - x₀‖ ^ 2 with hC
  have key : ∀ n : ℕ, (1 - 1 / (n + 1 : ℝ)) * C ≤ f x - f x₀ := by
    intro n
    set t : ℝ := 1 / (n + 1 : ℝ) with ht
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht0 : 0 < t := by rw [ht]; positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hn1]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h := hf.2 (mem_univ x) (mem_univ x₀) ht0.le (by linarith : (0 : ℝ) ≤ 1 - t)
      (by ring)
    have hlow := hmin (t • x + (1 - t) • x₀)
    simp only [smul_eq_mul] at h
    rw [← hC] at h
    have h2 : t * ((1 - t) * C) ≤ t * (f x - f x₀) := by nlinarith [hlow, h]
    exact le_of_mul_le_mul_left h2 ht0
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ)) * C) atTop (𝓝 ((1 - 0) * C)) := by
    exact ((tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat).mul
      tendsto_const_nhds)
  have := le_of_tendsto hlim (Eventually.of_forall key)
  simpa using this

/-- **Theorem L2 (basin localisation for strongly convex losses).**  For a
`μ`-strongly convex `L`-Lipschitz loss, every weight configuration that is optimal
*within the lattice* lies within `√(2Lr/μ)` of the true optimum: quantization
cannot move the basin of attraction. -/
theorem strongConvex_quantized_minimizer_close {μ : ℝ} (hμ : 0 < μ) {L : NNReal}
    {f : E → ℝ} {x₀ ŵ : E} (hf : StrongConvexOn univ μ f) (hL : LipschitzWith L f)
    (Q : Quantizer E) (hmin : ∀ x, f x₀ ≤ f x) (hlat : ∀ x, f ŵ ≤ f (Q.toFun x)) :
    ‖ŵ - x₀‖ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) :=
  quantized_minimizer_close hμ hL Q (quadratic_growth_of_strongConvexOn hf hmin) hlat

/-! ## Section 2: the curvature modulus survives quantization -/

/-- `ApproxStrongConvexOn ε μ s g`: `μ`-strong convexity up to an additive defect `ε`. -/
-- [dropped: platform already declares ApproxStrongConvexOn]
theorem quantized_approxStrongConvex {μ : ℝ} {L : NNReal} {f : E → ℝ}
    (hf : StrongConvexOn univ μ f) (hL : LipschitzWith L f) (Q : Quantizer E) :
    ApproxStrongConvexOn (2 * (L : ℝ) * Q.radius) μ univ (f ∘ Q.toFun) := by
  intro x _ y _ a b ha hb hab
  have hmid : f (Q.toFun (a • x + b • y)) ≤ f (a • x + b • y) + (L : ℝ) * Q.radius :=
    loss_quantize_le hL Q _
  have hstrong := hf.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hstrong
  have hx : f x ≤ f (Q.toFun x) + (L : ℝ) * Q.radius := loss_le_quantize hL Q x
  have hy : f y ≤ f (Q.toFun y) + (L : ℝ) * Q.radius := loss_le_quantize hL Q y
  have hax : a * f x ≤ a * (f (Q.toFun x) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left hx ha
  have hby : b * f y ≤ b * (f (Q.toFun y) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left hy hb
  have hsum : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius) = (L : ℝ) * Q.radius := by
    have h : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius)
        = (a + b) * ((L : ℝ) * Q.radius) := by ring
    rw [h, hab, one_mul]
  simp only [Function.comp_apply]
  nlinarith [hmid, hstrong, hax, hby, hsum]

/-! ## Section 3: the optimal value is preserved -/

omit [NormedSpace ℝ E] in
/-- **Theorem L4 (optimal-value stability).**  The optimum of the lattice-restricted
training problem and the optimum of the continuous problem differ by at most
`L·r`.  Quantization therefore preserves the *value* of the global optimum, the
coarsest invariant of the loss landscape. -/
theorem lattice_infimum_close [Nonempty E] {L : NNReal} {f : E → ℝ}
    (hL : LipschitzWith L f) (Q : Quantizer E) (hbdd : BddBelow (Set.range f)) :
    sInf (Set.range f) ≤ sInf (f '' Set.range Q.toFun) ∧
      sInf (f '' Set.range Q.toFun) ≤ sInf (Set.range f) + (L : ℝ) * Q.radius := by
  have hsub : f '' Set.range Q.toFun ⊆ Set.range f := by
    rintro _ ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨Q.toFun x, rfl⟩
  have hne : (f '' Set.range Q.toFun).Nonempty :=
    ⟨f (Q.toFun (Classical.arbitrary E)), ⟨Q.toFun (Classical.arbitrary E),
      ⟨Classical.arbitrary E, rfl⟩, rfl⟩⟩
  have hbdd' : BddBelow (f '' Set.range Q.toFun) := hbdd.mono hsub
  refine ⟨csInf_le_csInf hbdd hne hsub, ?_⟩
  have hlb : ∀ z ∈ Set.range f, sInf (f '' Set.range Q.toFun) - (L : ℝ) * Q.radius ≤ z := by
    rintro _ ⟨x, rfl⟩
    have h1 : sInf (f '' Set.range Q.toFun) ≤ f (Q.toFun x) :=
      csInf_le hbdd' ⟨Q.toFun x, ⟨x, rfl⟩, rfl⟩
    have h2 : f (Q.toFun x) ≤ f x + (L : ℝ) * Q.radius := loss_quantize_le hL Q x
    linarith
  have := le_csInf (Set.range_nonempty f) hlb
  linarith

end QuantizedWeightLattices.Landscape
-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLatticesSharpConstant.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, V:
# the exact convexity defect of nearest-point grid quantization

This file closes the first open conjecture of `FUTURE_DIRECTIONS.md`
("the sharp constant is `L·r`, not `2·L·r`, for *nearest-point* quantizers").

The conjecture is **false**, and it is refuted here by an explicit convex
`1`-Lipschitz loss:

* `targetLoss_defect_ge` — the "distance to the target weight" loss
  `f w = |w − δ|` composed with `δ`-grid rounding has convexity defect
  `≥ (1 − 1/n)·δ` for every `n ≥ 3`, hence
* `gridRound_defect_ge` — defect `≥ δ = 2·L·r`.  Combined with Theorem A
  (`quantized_approxConvex`) the sharp constant for the nearest-point grid
  quantizer is **exactly** `2·L·r` (`grid_defect_constant_exact`), and the
  conjectured `L·r` bound fails (`grid_defect_Lr_refuted`).

The earlier computational scans missed this because they only tested losses
(`|x|`, `x²`, a two-kink loss) that are *symmetric around a grid point*; the
extremal configuration needs a strongly unbalanced convex combination `a → 1`
together with a loss that decreases across the offending grid cell.

The failure is however confined to unbalanced combinations.  The second half of
the file proves the complementary **positive** result:

* `two_round_midpoint_sub_le` — the arithmetic heart, an integer parity
  statement: `|round X + round Y − 2·round((X+Y)/2)| ≤ 1`;
* `gridRound_midpoint_dist` — hence rounding the midpoint of two weights differs
  from the midpoint of the two rounded weights by at most `δ/2`;
* `quantizeTensor_midpoint_defect` — hence for *weight averaging* (`a = b = ½`,
  the "model soup" regime) the entrywise-quantized landscape of a convex
  `L`-Lipschitz loss has defect at most `L·δ/2 = L·r`, **half** the general
  bound, and that constant is sharp (`midpoint_constant_sharp`).

So the true picture is: defect `= 2·L·r` in general, `= L·r` on balanced
combinations.
-/

namespace QuantizedWeightLattices.SharpConstant

open QuantizedWeightLattices QuantizedWeightLattices.Sharp Set

/-! ## Section 1: an integer parity lemma for nearest-point rounding -/

/-- **Parity of nearest-point rounding.**  For any two reals, the sum of their
roundings and twice the rounding of their mean differ by at most one.  This is a
genuine arithmetic constraint: it forbids the two endpoints and the midpoint of a
segment from being rounded "in opposite directions" simultaneously. -/
lemma two_round_midpoint_sub_le (X Y : ℝ) :
    |round X + round Y - 2 * round ((X + Y) / 2)| ≤ 1 := by
  have hX1 : X - 1 / 2 < ((round X : ℤ) : ℝ) := sub_half_lt_round X
  have hX2 : ((round X : ℤ) : ℝ) ≤ X + 1 / 2 := round_le_add_half X
  have hY1 : Y - 1 / 2 < ((round Y : ℤ) : ℝ) := sub_half_lt_round Y
  have hY2 : ((round Y : ℤ) : ℝ) ≤ Y + 1 / 2 := round_le_add_half Y
  have hM1 : (X + Y) / 2 - 1 / 2 < ((round ((X + Y) / 2) : ℤ) : ℝ) := sub_half_lt_round _
  have hM2 : ((round ((X + Y) / 2) : ℤ) : ℝ) ≤ (X + Y) / 2 + 1 / 2 := round_le_add_half _
  -- upper bound: `2w < p + q + 2`
  have hup : ((2 * round ((X + Y) / 2) : ℤ) : ℝ) < ((round X + round Y + 2 : ℤ) : ℝ) := by
    push_cast; linarith
  have hup' : 2 * round ((X + Y) / 2) < round X + round Y + 2 := by exact_mod_cast hup
  -- lower bound: `p + q - 2 < 2w`
  have hlo : ((round X + round Y - 2 : ℤ) : ℝ) < ((2 * round ((X + Y) / 2) : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo' : round X + round Y - 2 < 2 * round ((X + Y) / 2) := by exact_mod_cast hlo
  exact abs_le.2 ⟨by omega, by omega⟩

/-- **Midpoint stability of grid quantization.**  Rounding the midpoint of two
weights and averaging the two rounded weights differ by at most the covering
radius `δ/2` — *not* `δ`, which is the general bound for the distance between
`Q(a x + b y)` and `a Q x + b Q y`. -/
lemma gridRound_midpoint_dist {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |gridRound δ ((x + y) / 2) - (gridRound δ x + gridRound δ y) / 2| ≤ δ / 2 := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have harg : (x + y) / 2 / δ = (x / δ + y / δ) / 2 := by field_simp
  have key : |round (x / δ) + round (y / δ) - 2 * round ((x / δ + y / δ) / 2)| ≤ 1 :=
    two_round_midpoint_sub_le (x / δ) (y / δ)
  have keyR : |((round (x / δ) + round (y / δ)
      - 2 * round ((x / δ + y / δ) / 2) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast key
  have hrepr : gridRound δ ((x + y) / 2) - (gridRound δ x + gridRound δ y) / 2
      = -(δ / 2) * ((round (x / δ) + round (y / δ)
          - 2 * round ((x / δ + y / δ) / 2) : ℤ) : ℝ) := by
    simp only [gridRound, harg]
    push_cast
    ring
  rw [hrepr, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < δ / 2)]
  calc δ / 2 * |((round (x / δ) + round (y / δ)
        - 2 * round ((x / δ + y / δ) / 2) : ℤ) : ℝ)|
      ≤ δ / 2 * 1 := mul_le_mul_of_nonneg_left keyR (by positivity)
    _ = δ / 2 := by ring

/-! ## Section 2: the midpoint (weight-averaging) defect is only `L·r` -/

section Tensor

variable {ι : Type*} [Fintype ι]

/-- Entrywise version of `gridRound_midpoint_dist`: quantizing the average of two
weight tensors is within `δ/2` (sup norm) of the average of the two quantized
tensors. -/
lemma quantizeTensor_midpoint_dist {δ : ℝ} (hδ : 0 < δ) (W V : ι → ℝ) :
    ‖quantizeTensor δ ((1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V)
      - ((1 / 2 : ℝ) • quantizeTensor δ W + (1 / 2 : ℝ) • quantizeTensor δ V)‖ ≤ δ / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := gridRound_midpoint_dist hδ (W i) (V i)
  have hi : ((1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V) i = (W i + V i) / 2 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e : (quantizeTensor δ ((1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V)
      - ((1 / 2 : ℝ) • quantizeTensor δ W + (1 / 2 : ℝ) • quantizeTensor δ V)) i
      = gridRound δ ((W i + V i) / 2) - (gridRound δ (W i) + gridRound δ (V i)) / 2 := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, quantizeTensor, hi]
    ring
  rw [Real.norm_eq_abs, e]
  exact h

variable {L : NNReal} {f : (ι → ℝ) → ℝ}

/-- **Theorem S7 (weight averaging is only `L·r`-nonconvex).**  For a convex
`L`-Lipschitz loss on weight tensors, the entrywise `δ`-grid quantized landscape
satisfies the convexity inequality at the *midpoint* with defect at most
`L·δ/2 = L·r`, i.e. half of the general bound `2·L·r` of Theorem A.

Interpretation: averaging two quantized checkpoints ("model soup") can lose only
half as much landscape convexity as an arbitrary interpolation. -/
theorem quantizeTensor_midpoint_defect (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    {δ : ℝ} (hδ : 0 < δ) (W V : ι → ℝ) :
    f (quantizeTensor δ ((1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V))
      ≤ (1 / 2 : ℝ) * f (quantizeTensor δ W) + (1 / 2 : ℝ) * f (quantizeTensor δ V)
        + (L : ℝ) * (δ / 2) := by
  set A : ι → ℝ := quantizeTensor δ ((1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V) with hA
  set B : ι → ℝ := (1 / 2 : ℝ) • quantizeTensor δ W + (1 / 2 : ℝ) • quantizeTensor δ V with hB
  have hdist : ‖A - B‖ ≤ δ / 2 := quantizeTensor_midpoint_dist hδ W V
  have hlip : |f A - f B| ≤ (L : ℝ) * ‖A - B‖ := abs_sub_le_lipschitz hL A B
  have hmul : (L : ℝ) * ‖A - B‖ ≤ (L : ℝ) * (δ / 2) :=
    mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  have hAB : f A ≤ f B + (L : ℝ) * (δ / 2) := by
    have := (abs_le.1 (hlip.trans hmul)).2
    linarith
  have hconv : f B ≤ (1 / 2 : ℝ) * f (quantizeTensor δ W)
      + (1 / 2 : ℝ) * f (quantizeTensor δ V) :=
    hf.2 (mem_univ _) (mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  linarith

end Tensor

/-- The scalar case of `quantizeTensor_midpoint_defect`, stated directly for
`gridRound` on `ℝ`. -/
theorem gridRound_midpoint_defect {L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    f (gridRound δ ((x + y) / 2))
      ≤ (1 / 2 : ℝ) * f (gridRound δ x) + (1 / 2 : ℝ) * f (gridRound δ y)
        + (L : ℝ) * (δ / 2) := by
  have hdist : |gridRound δ ((x + y) / 2)
      - ((1 / 2 : ℝ) * gridRound δ x + (1 / 2 : ℝ) * gridRound δ y)| ≤ δ / 2 := by
    have h := gridRound_midpoint_dist hδ x y
    have e : (gridRound δ x + gridRound δ y) / 2
        = (1 / 2 : ℝ) * gridRound δ x + (1 / 2 : ℝ) * gridRound δ y := by ring
    rwa [e] at h
  set A : ℝ := gridRound δ ((x + y) / 2) with hA
  set B : ℝ := (1 / 2 : ℝ) * gridRound δ x + (1 / 2 : ℝ) * gridRound δ y with hB
  have hlip : |f A - f B| ≤ (L : ℝ) * ‖A - B‖ := abs_sub_le_lipschitz hL A B
  have hmul : (L : ℝ) * ‖A - B‖ ≤ (L : ℝ) * (δ / 2) := by
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  have hAB : f A ≤ f B + (L : ℝ) * (δ / 2) := by
    have := (abs_le.1 (hlip.trans hmul)).2
    linarith
  have hconv : f B ≤ (1 / 2 : ℝ) * f (gridRound δ x) + (1 / 2 : ℝ) * f (gridRound δ y) := by
    have := hf.2 (mem_univ (gridRound δ x)) (mem_univ (gridRound δ y))
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    simpa [hB, smul_eq_mul] using this
  linarith

/-- **Sharpness of the midpoint constant.**  The constant `L·δ/2` of
`gridRound_midpoint_defect` cannot be lowered: the convex `1`-Lipschitz loss `|·|`
attains it at the weights `2δ/5` and `3δ/5`. -/
theorem midpoint_constant_sharp {δ : ℝ} (hδ : 0 < δ) :
    |gridRound δ ((2 * δ / 5 + 3 * δ / 5) / 2)|
      = (1 / 2 : ℝ) * |gridRound δ (2 * δ / 5)| + (1 / 2 : ℝ) * |gridRound δ (3 * δ / 5)|
        + ((1 : NNReal) : ℝ) * (δ / 2) := by
  have harg : (2 * δ / 5 + 3 * δ / 5) / 2 = δ / 2 := by ring
  rw [harg, gridRound_half hδ, gridRound_two_fifths hδ, gridRound_three_fifths hδ,
    abs_of_pos hδ, abs_zero]
  push_cast
  ring

/-! ## Section 3: refutation of the `L·r` conjecture for unbalanced combinations

The loss is `f w = |w − δ|`, the distance to the target weight `δ` (itself a grid
point); it is convex and `1`-Lipschitz.  The two sample weights are `δ/2` and
`−δ/2`, which round *away from each other* to `δ` and `0`; their convex
combination with weights `a = 1 − 1/n` and `b = 1/n` sits just below the rounding
threshold `δ/2` and therefore rounds *down* to `0`, where the loss is maximal. -/

/-- The "distance to the target weight `c`" loss. -/
-- [dropped: platform already declares targetLoss]
lemma convexOn_targetLoss (c : ℝ) : ConvexOn ℝ univ (targetLoss c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  have hx : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    simp only [smul_eq_mul]; linarith
  simp only [targetLoss, hx]
  calc |a • (x - c) + b • (y - c)| ≤ |a • (x - c)| + |b • (y - c)| := abs_add_le _ _
    _ = a * |x - c| + b * |y - c| := by
        simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

lemma lipschitzWith_targetLoss (c : ℝ) : LipschitzWith 1 (targetLoss c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := abs_abs_sub_abs_le_abs_sub (x - c) (y - c)
  have e : (x - c) - (y - c) = x - y := by ring
  rw [e] at h
  simpa [Real.dist_eq, targetLoss] using h

lemma gridRound_neg_half {δ : ℝ} (hδ : 0 < δ) : gridRound δ (-(δ / 2)) = 0 := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : -(δ / 2) / δ = -(1 / 2) := by field_simp
  simp [gridRound, hx]

/-- The critical weight `δ/2 − δ/n` sits just below the rounding threshold and
therefore rounds *down* to `0` (for `n ≥ 3`). -/
lemma gridRound_just_below_half {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n) :
    gridRound δ (δ / 2 - δ / n) = 0 := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hfac : δ / 2 - δ / (n : ℝ) = δ * (1 / 2 - 1 / (n : ℝ)) := by
    field_simp
  have hx : (δ / 2 - δ / n) / δ = 1 / 2 - 1 / (n : ℝ) := by
    rw [hfac, mul_comm, mul_div_assoc, div_self hne, mul_one]
  have hinv_pos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hinv_le : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
  have hlow : (0 : ℝ) ≤ 1 / 2 - 1 / (n : ℝ) + 1 / 2 := by linarith
  have hhigh : 1 / 2 - 1 / (n : ℝ) + 1 / 2 < 1 := by linarith
  have hr : round (1 / 2 - 1 / (n : ℝ)) = 0 := by
    rw [round_eq]
    exact Int.floor_eq_zero_iff.2 (Set.mem_Ico.2 ⟨hlow, hhigh⟩)
  rw [gridRound, hx, hr]
  simp

/-- **Defect lower bound for the target loss.**  For every `n ≥ 3` the convexity
defect of the `δ`-grid quantized target loss is at least `(1 − 1/n)·δ`. -/
theorem targetLoss_defect_ge {δ ε : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n)
    (h : ApproxConvexOn ε univ (targetLoss δ ∘ gridRound δ)) :
    δ - δ / n ≤ ε := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv_pos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hinv_le : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
  have hcomb : (1 - 1 / (n : ℝ)) • (δ / 2) + (1 / (n : ℝ)) • (-(δ / 2)) = δ / 2 - δ / n := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have key := h (mem_univ (δ / 2)) (mem_univ (-(δ / 2))) (by linarith : (0:ℝ) ≤ 1 - 1 / (n:ℝ))
    hinv_pos.le (by ring)
  rw [hcomb] at key
  simp only [Function.comp_apply, targetLoss, gridRound_just_below_half hδ hn,
    gridRound_half hδ, gridRound_neg_half hδ] at key
  rw [show (0 : ℝ) - δ = -δ by ring, abs_neg, abs_of_pos hδ,
    show δ - δ = (0:ℝ) by ring, abs_zero] at key
  have hdn : (1 / (n : ℝ)) * δ = δ / n := by field_simp
  nlinarith [key, hdn]

/-- **Theorem S8 (the constant `2·L·r` is exactly optimal, even for nearest-point
grid quantization).**  Any approximate-convexity certificate valid for all convex
`1`-Lipschitz losses and the `δ`-grid quantizer must have defect at least
`δ = 2·L·r`.  This *refutes* Conjecture 1 of `FUTURE_DIRECTIONS.md`. -/
theorem gridRound_defect_ge {δ ε : ℝ} (hδ : 0 < δ)
    (h : ApproxConvexOn ε univ (targetLoss δ ∘ gridRound δ)) : δ ≤ ε := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < δ - ε := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (δ / (δ - ε))
  set n : ℕ := max m 3 with hn
  have hn3 : 3 ≤ n := le_max_right m 3
  have hnm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 3
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) (lt_of_lt_of_le hm hnm)
  have hlt : δ / (δ - ε) < (n : ℝ) := lt_of_lt_of_le hm hnm
  have hkey : δ - δ / n ≤ ε := targetLoss_defect_ge hδ hn3 h
  have h1 : δ < (n : ℝ) * (δ - ε) := by
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  have h2 : δ / (n : ℝ) < δ - ε := by
    rw [div_lt_iff₀ hn0]
    linarith
  linarith

/-- The conjectured improvement of the general defect constant to `L·r` is false. -/
theorem grid_defect_Lr_refuted {δ : ℝ} (hδ : 0 < δ) :
    ¬ ApproxConvexOn (δ / 2) univ (targetLoss δ ∘ gridRound δ) := by
  intro h
  have := gridRound_defect_ge hδ h
  linarith

/-- **The exact defect constant of nearest-point grid quantization.**  For the
scalar `δ`-grid quantizer (covering radius `r = δ/2`) and convex `1`-Lipschitz
losses, the optimal approximate-convexity constant is exactly `δ = 2·L·r`:
Theorem A gives it, and no smaller value works. -/
theorem grid_defect_constant_exact {δ : ℝ} (hδ : 0 < δ) :
    ApproxConvexOn δ univ (targetLoss δ ∘ gridRound δ) ∧
      ∀ ε : ℝ, ApproxConvexOn ε univ (targetLoss δ ∘ gridRound δ) → δ ≤ ε := by
  refine ⟨?_, fun ε hε => gridRound_defect_ge hδ hε⟩
  have h := quantized_approxConvex (convexOn_targetLoss δ) (lipschitzWith_targetLoss δ)
    (scalarQuantizer hδ)
  have hrad : 2 * ((1 : NNReal) : ℝ) * (scalarQuantizer hδ).radius = δ := by
    show 2 * ((1 : NNReal) : ℝ) * (δ / 2) = δ
    push_cast
    ring
  rwa [hrad] at h

/-! ## Section 4: the finite-precision convexity audit

Theorem E of `QuantizedWeightLattices.lean` recovers *exact* convexity of the
continuous loss from an infinite tower of quantized landscapes with vanishing
defects.  The following two statements are its *finite* counterpart, and they
resolve the analytic half of Conjecture 5 of `FUTURE_DIRECTIONS.md`: a single
precision already certifies convexity of the continuous loss up to `2·L·r`, and
the correspondence is two-sided — quantization changes the convexity defect of an
`L`-Lipschitz landscape by at most `2·L·r`, in either direction. -/

section Audit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}

/-- **Quantization increases the defect by at most `2·L·r`** (Theorem A with the
exact-convexity hypothesis relaxed to `ε`-approximate convexity). -/
theorem quantized_approxConvexOn_of_approxConvexOn (hL : LipschitzWith L f) (Q : Quantizer E)
    {ε : ℝ} (h : ApproxConvexOn ε univ f) :
    ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by
  intro x _ y _ a b ha hb hab
  have hmid : f (Q.toFun (a • x + b • y)) ≤ f (a • x + b • y) + (L : ℝ) * Q.radius :=
    loss_quantize_le hL Q _
  have hconv : f (a • x + b • y) ≤ a * f x + b * f y + ε := h (mem_univ x) (mem_univ y) ha hb hab
  have hax : a * f x ≤ a * (f (Q.toFun x) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left (loss_le_quantize hL Q x) ha
  have hby : b * f y ≤ b * (f (Q.toFun y) + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left (loss_le_quantize hL Q y) hb
  have hsum : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius) = (L : ℝ) * Q.radius := by
    rw [← add_mul, hab, one_mul]
  simp only [Function.comp_apply]
  nlinarith [hmid, hconv, hax, hby, hsum]

/-- **Theorem F (finite-precision convexity certification).**  Conversely, if the
quantized landscape of an `L`-Lipschitz loss is `ε`-approximately convex at a
*single* precision with covering radius `r`, then the continuous loss is
`(ε + 2·L·r)`-approximately convex.  In particular a *convex* quantized landscape
(`ε = 0`) certifies convexity of the true loss up to `2·L·r`; letting `r → 0`
along a refining tower recovers Theorem E. -/
theorem approxConvexOn_of_quantized (hL : LipschitzWith L f) (Q : Quantizer E) {ε : ℝ}
    (h : ApproxConvexOn ε univ (f ∘ Q.toFun)) :
    ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ f := by
  intro x _ y _ a b ha hb hab
  have hmid : f (a • x + b • y) ≤ f (Q.toFun (a • x + b • y)) + (L : ℝ) * Q.radius :=
    loss_le_quantize hL Q _
  have hq : f (Q.toFun (a • x + b • y)) ≤ a * f (Q.toFun x) + b * f (Q.toFun y) + ε := by
    have := h (mem_univ x) (mem_univ y) ha hb hab
    simpa [Function.comp_apply] using this
  have hax : a * f (Q.toFun x) ≤ a * (f x + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left (loss_quantize_le hL Q x) ha
  have hby : b * f (Q.toFun y) ≤ b * (f y + (L : ℝ) * Q.radius) :=
    mul_le_mul_of_nonneg_left (loss_quantize_le hL Q y) hb
  have hsum : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius) = (L : ℝ) * Q.radius := by
    rw [← add_mul, hab, one_mul]
  nlinarith [hmid, hq, hax, hby, hsum]

/-- **Theorem G (two-sided audit).**  For an `L`-Lipschitz loss the convexity
defect is a `2·L·r`-Lipschitz invariant of quantization: certificates transfer in
both directions with the same loss `2·L·r`, which by `grid_defect_constant_exact`
is optimal for nearest-point grid quantization. -/
theorem convexity_audit_two_sided (hL : LipschitzWith L f) (Q : Quantizer E) {ε : ℝ} :
    (ApproxConvexOn ε univ f → ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun)) ∧
      (ApproxConvexOn ε univ (f ∘ Q.toFun) →
        ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ f) :=
  ⟨quantized_approxConvexOn_of_approxConvexOn hL Q, approxConvexOn_of_quantized hL Q⟩

/-- A convex quantized landscape certifies `2·L·r`-approximate convexity of the
continuous loss. -/
theorem approxConvexOn_of_convex_quantized (hL : LipschitzWith L f) (Q : Quantizer E)
    (h : ConvexOn ℝ univ (f ∘ Q.toFun)) :
    ApproxConvexOn (2 * (L : ℝ) * Q.radius) univ f := by
  have := approxConvexOn_of_quantized hL Q h.approxConvexOn
  simpa using this

end Audit

/-! ## Section 5: the denominator law

The two extreme cases proved above — defect `L·r` for the balanced weight `a = 1/2`
and defect `→ 2·L·r` along `a = 1 − 1/n` — are the first instances of a single
**arithmetic law**: the sharp convexity defect at an interpolation weight
`a = k/q` (in lowest terms) is governed by the *denominator* `q`,

  `defect ≤ (1 − 1/q) · L · δ = (1 − 1/q) · 2·L·r`.

The reason is purely number-theoretic: the discrepancy
`A = a·Qx + (1−a)·Qy − Q(a x + (1−a) y)` is a multiple of `δ/q` (all three
roundings are lattice points and `a` has denominator `q`), while three
covering-radius estimates force `|A| < δ`; an integer strictly smaller than `q` is
at most `q − 1`.  The convex-analytic half converts `|A|` into a defect bound.

For `q = 2` this returns `L·δ/2 = L·r`, and the bound is attained for every `q`
at `a = (q−1)/q` (`targetLoss_defect_eq`), so the law is sharp along that family. -/

section DenominatorLaw

lemma round_monotone : Monotone (round : ℝ → ℤ) := by
  intro x y h
  simp only [round_eq]
  exact Int.floor_le_floor (by linarith)

lemma gridRound_monotone {δ : ℝ} (hδ : 0 < δ) : Monotone (gridRound δ) := by
  intro x y h
  have hdiv : x / δ ≤ y / δ := by gcongr
  have hround : (round (x / δ) : ℝ) ≤ (round (y / δ) : ℝ) := by
    exact_mod_cast round_monotone hdiv
  simpa [gridRound] using mul_le_mul_of_nonneg_left hround hδ.le

/-- **Convex-analytic half of the denominator law.**  If `w` lies between `u` and
`v`, the convexity defect of an `L`-Lipschitz convex `f` at the triple `(u, v, w)`
with weight `a` is bounded by `L` times the *discrepancy* `|a u + (1−a) v − w|`. -/
lemma convex_defect_le_discrepancy {L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {u v w a : ℝ} (hw : w ∈ Set.Icc (min u v) (max u v)) :
    f w - (a * f u + (1 - a) * f v) ≤ (L : ℝ) * |a * u + (1 - a) * v - w| := by
  rw [← segment_eq_Icc'] at hw
  obtain ⟨s, t, hs, ht, hst, hw'⟩ := hw
  have hwe : w = s * u + t * v := by rw [← hw']; simp [smul_eq_mul]
  have ht' : t = 1 - s := by linarith
  have hfw : f w ≤ s * f u + (1 - s) * f v := by
    have hconv := hf.2 (mem_univ u) (mem_univ v) hs ht hst
    rw [hwe, ht']
    simpa [smul_eq_mul, ht'] using hconv
  have hA : a * u + (1 - a) * v - w = (a - s) * (u - v) := by rw [hwe, ht']; ring
  have hlip : |f v - f u| ≤ (L : ℝ) * |v - u| := by
    simpa [Real.norm_eq_abs] using abs_sub_le_lipschitz hL v u
  calc f w - (a * f u + (1 - a) * f v) ≤ (a - s) * (f v - f u) := by nlinarith [hfw]
    _ ≤ |(a - s) * (f v - f u)| := le_abs_self _
    _ = |a - s| * |f v - f u| := abs_mul _ _
    _ ≤ |a - s| * ((L : ℝ) * |v - u|) := by
        exact mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
    _ = (L : ℝ) * (|a - s| * |u - v|) := by rw [abs_sub_comm v u]; ring
    _ = (L : ℝ) * |a * u + (1 - a) * v - w| := by rw [hA, abs_mul]

/-- **Covering-radius half.**  The rounding discrepancy of a strictly convex
combination is *strictly* smaller than one full mesh. -/
lemma discrepancy_lt_mesh {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x y : ℝ) :
    |a * gridRound δ x + (1 - a) * gridRound δ y
      - gridRound δ (a * x + (1 - a) * y)| < δ := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hM : (a * x + (1 - a) * y) / δ = a * (x / δ) + (1 - a) * (y / δ) := by
    field_simp
  set X : ℝ := x / δ with hX
  set Y : ℝ := y / δ with hY
  set M : ℝ := a * X + (1 - a) * Y with hMdef
  have hp1 : X - 1 / 2 < ((round X : ℤ) : ℝ) := sub_half_lt_round X
  have hp2 : ((round X : ℤ) : ℝ) ≤ X + 1 / 2 := round_le_add_half X
  have hr1 : Y - 1 / 2 < ((round Y : ℤ) : ℝ) := sub_half_lt_round Y
  have hr2 : ((round Y : ℤ) : ℝ) ≤ Y + 1 / 2 := round_le_add_half Y
  have hs1 : M - 1 / 2 < ((round M : ℤ) : ℝ) := sub_half_lt_round M
  have hs2 : ((round M : ℤ) : ℝ) ≤ M + 1 / 2 := round_le_add_half M
  have hup : a * ((round X : ℤ) : ℝ) + (1 - a) * ((round Y : ℤ) : ℝ) ≤ M + 1 / 2 := by
    have h1 : a * ((round X : ℤ) : ℝ) ≤ a * (X + 1 / 2) :=
      mul_le_mul_of_nonneg_left hp2 ha0.le
    have h2 : (1 - a) * ((round Y : ℤ) : ℝ) ≤ (1 - a) * (Y + 1 / 2) :=
      mul_le_mul_of_nonneg_left hr2 (by linarith)
    have : a * (X + 1 / 2) + (1 - a) * (Y + 1 / 2) = M + 1 / 2 := by rw [hMdef]; ring
    linarith
  have hlow : M - 1 / 2 < a * ((round X : ℤ) : ℝ) + (1 - a) * ((round Y : ℤ) : ℝ) := by
    have h1 : a * (X - 1 / 2) < a * ((round X : ℤ) : ℝ) := mul_lt_mul_of_pos_left hp1 ha0
    have h2 : (1 - a) * (Y - 1 / 2) < (1 - a) * ((round Y : ℤ) : ℝ) :=
      mul_lt_mul_of_pos_left hr1 (by linarith)
    have : a * (X - 1 / 2) + (1 - a) * (Y - 1 / 2) = M - 1 / 2 := by rw [hMdef]; ring
    linarith
  have hrepr : a * gridRound δ x + (1 - a) * gridRound δ y - gridRound δ (a * x + (1 - a) * y)
      = δ * (a * ((round X : ℤ) : ℝ) + (1 - a) * ((round Y : ℤ) : ℝ)
          - ((round M : ℤ) : ℝ)) := by
    simp only [gridRound, hM, ← hX, ← hY]
    ring
  rw [hrepr, abs_mul, abs_of_pos hδ]
  have hbound : |a * ((round X : ℤ) : ℝ) + (1 - a) * ((round Y : ℤ) : ℝ)
      - ((round M : ℤ) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  nlinarith [hbound]

/-- **Arithmetic half of the denominator law.**  For an interpolation weight with
denominator `q` the discrepancy is a multiple of `δ/q` and strictly below `δ`,
hence at most `(1 − 1/q)·δ`. -/
lemma discrepancy_le_denominator {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q)
    (x y : ℝ) :
    |(k / q : ℝ) * gridRound δ x + (1 - (k / q : ℝ)) * gridRound δ y
      - gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y)| ≤ δ * (1 - 1 / q) := by
  have hq0 : 0 < q := lt_trans hk0 hkq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkqR : (k : ℝ) < (q : ℝ) := by exact_mod_cast hkq
  have ha0 : (0 : ℝ) < (k / q : ℝ) := by positivity
  have ha1 : (k / q : ℝ) < 1 := by rw [div_lt_one hqR]; exact hkqR
  have hlt := discrepancy_lt_mesh hδ ha0 ha1 x y
  -- the discrepancy is `δ/q` times an integer
  set J : ℤ := (k : ℤ) * round (x / δ) + ((q : ℤ) - (k : ℤ)) * round (y / δ)
      - (q : ℤ) * round (((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y) / δ) with hJ
  have hrepr : (k / q : ℝ) * gridRound δ x + (1 - (k / q : ℝ)) * gridRound δ y
      - gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y) = δ / q * (J : ℝ) := by
    simp only [gridRound, hJ]
    push_cast
    field_simp
  rw [hrepr] at hlt ⊢
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < δ / q)] at hlt ⊢
  have hJlt : |(J : ℝ)| < (q : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have : δ / q * (q : ℝ) ≤ δ / q * |(J : ℝ)| :=
      mul_le_mul_of_nonneg_left hcon (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hqR)] at this
    linarith
  have hJle : |J| ≤ (q : ℤ) - 1 := by
    have : |J| < (q : ℤ) := by
      have : ((|J| : ℤ) : ℝ) < ((q : ℤ) : ℝ) := by
        push_cast [Int.cast_abs]
        exact_mod_cast hJlt
      exact_mod_cast this
    omega
  have hJleR : |(J : ℝ)| ≤ (q : ℝ) - 1 := by
    have : ((|J| : ℤ) : ℝ) ≤ (((q : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hJle
    push_cast [Int.cast_abs] at this
    exact this
  calc δ / q * |(J : ℝ)| ≤ δ / q * ((q : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hJleR (by positivity)
    _ = δ * (1 - 1 / q) := by field_simp

/-- **The denominator law.**  For a convex `L`-Lipschitz loss, the `δ`-grid
quantized landscape satisfies the convexity inequality at every interpolation
weight `a = k/q` with defect at most `(1 − 1/q)·L·δ = (1 − 1/q)·2·L·r`.

Balanced weights (`q = 2`) lose only `L·r`; the general bound `2·L·r` is
approached only along weights of large denominator. -/
theorem gridRound_defect_denominator {L : NNReal} {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    (hL : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q) (hk : k ≤ q) (x y : ℝ) :
    f (gridRound δ ((k / q : ℝ) * x + (1 - (k / q : ℝ)) * y))
      ≤ (k / q : ℝ) * f (gridRound δ x) + (1 - (k / q : ℝ)) * f (gridRound δ y)
        + (L : ℝ) * (δ * (1 - 1 / q)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : 1 / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast hq
  have hnonneg : 0 ≤ (L : ℝ) * (δ * (1 - 1 / q)) := by
    have : (0 : ℝ) ≤ 1 - 1 / q := by linarith
    have := L.coe_nonneg
    positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero, one_mul, zero_add]
    linarith
  rcases eq_or_lt_of_le hk with hkq | hkq
  · subst hkq
    rw [div_self (ne_of_gt hqR)]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    linarith
  -- the generic case `0 < k < q`
  set a : ℝ := (k / q : ℝ) with ha
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hqR]
    exact_mod_cast hkq
  set u : ℝ := gridRound δ x with hu
  set v : ℝ := gridRound δ y with hv
  set w : ℝ := gridRound δ (a * x + (1 - a) * y) with hw
  have hmem : a * x + (1 - a) * y ∈ Set.Icc (min x y) (max x y) := by
    constructor
    · have h1 : min x y ≤ x := min_le_left x y
      have h2 : min x y ≤ y := min_le_right x y
      nlinarith
    · have h1 : x ≤ max x y := le_max_left x y
      have h2 : y ≤ max x y := le_max_right x y
      nlinarith
  have hwmem : w ∈ Set.Icc (min u v) (max u v) := by
    have hmono := gridRound_monotone hδ
    constructor
    · rw [hu, hv, ← hmono.map_min]
      exact hmono hmem.1
    · rw [hu, hv, ← hmono.map_max]
      exact hmono hmem.2
  have hdef := convex_defect_le_discrepancy hf hL (a := a) hwmem
  have hdisc := discrepancy_le_denominator hδ hk0 hkq x y
  have hmul : (L : ℝ) * |a * u + (1 - a) * v - w| ≤ (L : ℝ) * (δ * (1 - 1 / q)) :=
    mul_le_mul_of_nonneg_left hdisc L.coe_nonneg
  linarith

/-- **Sharpness of the denominator law at `a = (q−1)/q`.**  The witness family of
Section 3 realises the bound exactly: for the target loss and the weight
`1 − 1/n`, the defect equals `(1 − 1/n)·δ`. -/
theorem targetLoss_defect_eq {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n) :
    targetLoss δ (gridRound δ ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))))
        - ((1 - 1 / (n : ℝ)) * targetLoss δ (gridRound δ (δ / 2))
          + (1 / (n : ℝ)) * targetLoss δ (gridRound δ (-(δ / 2))))
      = δ * (1 - 1 / (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hcomb : (1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2)) = δ / 2 - δ / n := by
    field_simp
    ring
  rw [hcomb, gridRound_just_below_half hδ hn, gridRound_half hδ, gridRound_neg_half hδ]
  simp only [targetLoss]
  rw [show (0 : ℝ) - δ = -δ by ring, abs_neg, abs_of_pos hδ, show δ - δ = (0:ℝ) by ring,
    abs_zero]
  field_simp
  ring

end DenominatorLaw

end QuantizedWeightLattices.SharpConstant
-- ==== upstream: Packages/Catalog/Bridges/QuantizedWeightLatticesDenominatorSharp.lean ====
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, VI:
# the denominator law is exact — the defect spectrum at a rational mixing weight

`Bridges.QuantizedWeightLatticesSharpConstant` proved the **denominator law**: for a
convex `L`-Lipschitz loss and the `δ`-grid quantizer, the convexity defect at the
interpolation weight `a = k/q` is at most `(1 − 1/q)·L·δ`, and it exhibited a
witness attaining the bound only for `k = q − 1`.  Conjecture 1 of
`FUTURE_DIRECTIONS.md` asked whether the bound is attained for *every* `k`
coprime to `q`.

This file settles that conjecture **affirmatively, and in a stronger form**:

* `defect_spectrum` — for `gcd(k, q) = 1` and *every* `j` with `0 ≤ j < q` there is
  an explicit convex `1`-Lipschitz loss (a "distance to a target weight" loss) and
  an explicit pair of weights whose quantized convexity defect at mixing weight
  `k/q` equals **exactly** `δ·j/q`.  The whole arithmetic progression
  `(δ/q)·{0, 1, …, q−1}` is realised: the defect spectrum is the full rank-one
  lattice slice predicted by the arithmetic half of the denominator law.
* `denominator_constant_exact` — consequently the supremum of the defect over all
  convex `1`-Lipschitz losses at mixing weight `k/q` is attained and equals
  `(1 − 1/q)·δ`; formally an `IsGreatest` statement, so the constant of the
  denominator law is optimal for every residue `k` coprime to `q`.
* `denominator_constant_reduced` — for a general (not necessarily reduced) weight
  `k/q` the sharp constant is `(1 − gcd(k,q)/q)·δ`, i.e. only the *reduced*
  denominator matters.  Arithmetic, not size, of the mixing weight controls the
  loss of convexity.
* `quantizeTensor_defect_denominator` — the denominator law itself lifts from `ℝ`
  to whole weight tensors `ι → ℝ` with the sup norm: entrywise `δ`-grid
  quantization of a transformer's weights loses at most `(1 − 1/q)·L·δ` of
  convexity at any mixing weight of denominator `q`.
* `mesh_determined_by_defectSet`, `reducedDenominator_determined_by_defectSet` — a
  spectral converse: the achievable convexity defects are an arithmetic
  fingerprint.  They determine the mesh `δ` of the quantizer and the *reduced*
  denominator of the mixing weight, both recoverable from landscape measurements
  alone.

The mechanism: all three roundings are lattice points, so the discrepancy
`a·Qx + (1−a)·Qy − Q(a x + (1−a) y)` lies in `(δ/q)·ℤ`; its numerator is
`k·(round X − round Y) mod q`, and as `round X − round Y` ranges over `ℤ` this
covers all of `ℤ/qℤ` exactly when `gcd(k, q) = 1`.  Attainment is therefore a
covering statement for the cyclic group `ℤ/qℤ`, and the covering witnesses are
produced here by Bézout.
-/

namespace QuantizedWeightLattices.DenominatorSharp

open Set QuantizedWeightLattices QuantizedWeightLattices.SharpConstant

/-! ## Section 1: the covering lemma for `ℤ/qℤ` -/

/-- **Bézout covering.**  If `k` is invertible mod `q`, every residue `j` is of the
form `k·d` mod `q`.  This is the arithmetic input that makes the denominator law
attainable at *every* coprime residue. -/
lemma exists_mul_sub_dvd {k q : ℕ} (hcop : Nat.Coprime k q) (j : ℤ) :
    ∃ d : ℤ, (q : ℤ) ∣ ((k : ℤ) * d - j) := by
  have hco : IsCoprime (k : ℤ) (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by
    simpa [Int.gcd_natCast_natCast] using hcop)
  obtain ⟨u, v, huv⟩ := hco
  refine ⟨u * j, ⟨-(v * j), ?_⟩⟩
  have : (k : ℤ) * u = 1 - v * q := by linarith [huv]
  calc (k : ℤ) * (u * j) - j = ((k : ℤ) * u) * j - j := by ring
    _ = (1 - v * q) * j - j := by rw [this]
    _ = (q : ℤ) * -(v * j) := by ring

/-! ## Section 2: exact roundings of the witness points -/

/-- Rounding is exact on half-integers of the form `d − 1/2` (Lean's `round`
rounds halves upwards). -/
lemma round_int_sub_half (d : ℤ) : round ((d : ℝ) - 1 / 2) = d := by
  rw [round_eq]
  norm_num

lemma gridRound_int_sub_half {δ : ℝ} (hδ : 0 < δ) (d : ℤ) :
    gridRound δ (δ * ((d : ℝ) - 1 / 2)) = δ * (d : ℝ) := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : δ * ((d : ℝ) - 1 / 2) / δ = (d : ℝ) - 1 / 2 := by
    field_simp
  rw [gridRound, hx, round_int_sub_half]

/-- **The critical rounding.**  If `n = q·s + j` with `0 ≤ j < q`, the point
`n/q − 1/2` rounds to `s`: the fractional part `j/q` is *not* enough to push the
rounding up.  This is where the denominator `q` enters. -/
lemma round_ratio_sub_half {q : ℕ} (hq : 0 < q) {n s j : ℤ} (hn : n = (q : ℤ) * s + j)
    (hj0 : 0 ≤ j) (hjq : j < (q : ℤ)) : round ((n : ℝ) / (q : ℝ) - 1 / 2) = s := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hjR : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have hjqR : (j : ℝ) < (q : ℝ) := by exact_mod_cast hjq
  have hval : (n : ℝ) / (q : ℝ) = (s : ℝ) + (j : ℝ) / (q : ℝ) := by
    rw [hn]
    push_cast
    field_simp
  rw [round_eq, show (n : ℝ) / (q : ℝ) - 1 / 2 + 1 / 2 = (n : ℝ) / (q : ℝ) by ring, hval]
  have hfrac0 : (0 : ℝ) ≤ (j : ℝ) / (q : ℝ) := by positivity
  have hfrac1 : (j : ℝ) / (q : ℝ) < 1 := by rw [div_lt_one hqR]; exact hjqR
  rw [Int.floor_eq_iff]
  constructor <;> linarith

lemma gridRound_ratio_point {δ : ℝ} (hδ : 0 < δ) {q : ℕ} (hq : 0 < q) {n s j : ℤ}
    (hn : n = (q : ℤ) * s + j) (hj0 : 0 ≤ j) (hjq : j < (q : ℤ)) :
    gridRound δ (δ * ((n : ℝ) / (q : ℝ) - 1 / 2)) = δ * (s : ℝ) := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hx : δ * ((n : ℝ) / (q : ℝ) - 1 / 2) / δ = (n : ℝ) / (q : ℝ) - 1 / 2 := by
    field_simp
  rw [gridRound, hx, round_ratio_sub_half hq hn hj0 hjq]

/-! ## Section 3: the witness family realising an arbitrary lattice defect -/

/-- **Master witness.**  Fix a mixing weight `a = k/q` and integers `d, s, j` with
`k·d = q·s + j` and `0 ≤ j < q`.  Take the two weights `x = δ(d − 1/2)` and
`y = −δ/2`; they round to `δ·d` and `0`, while their `a`-combination
`δ(kd/q − 1/2)` rounds *down* to `δ·s`.  Against the target loss `|w − δ·C|` with
`C` large enough, the convexity defect of the quantized landscape is exactly
`δ·j/q`.

Every claim of this file is an instance of this computation. -/
lemma targetLoss_defect_witness {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q)
    {d s j C : ℤ} (hkd : (k : ℤ) * d = (q : ℤ) * s + j) (hj0 : 0 ≤ j) (hjq : j < (q : ℤ))
    (hCd : d ≤ C) (hCs : s ≤ C) (hC0 : 0 ≤ C) :
    targetLoss (δ * (C : ℝ))
        (gridRound δ (((k : ℝ) / q) * (δ * ((d : ℝ) - 1 / 2))
          + (1 - (k : ℝ) / q) * (-(δ / 2))))
      - (((k : ℝ) / q) * targetLoss (δ * (C : ℝ)) (gridRound δ (δ * ((d : ℝ) - 1 / 2)))
        + (1 - (k : ℝ) / q) * targetLoss (δ * (C : ℝ)) (gridRound δ (-(δ / 2))))
      = δ * (j : ℝ) / (q : ℝ) := by
  -- the mixing point is `δ·(kd/q − 1/2)`
  have hmix : ((k : ℝ) / q) * (δ * ((d : ℝ) - 1 / 2)) + (1 - (k : ℝ) / q) * (-(δ / 2))
      = δ * ((((k : ℤ) * d : ℤ) : ℝ) / (q : ℝ) - 1 / 2) := by
    push_cast
    field_simp
    ring
  rw [hmix, gridRound_ratio_point hδ hq hkd hj0 hjq, gridRound_int_sub_half hδ,
    gridRound_neg_half hδ]
  -- now evaluate the three losses
  have hCdR : (d : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCd
  have hCsR : (s : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCs
  have hC0R : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC0
  have e1 : targetLoss (δ * (C : ℝ)) (δ * (s : ℝ)) = δ * ((C : ℝ) - (s : ℝ)) := by
    simp only [targetLoss]
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have e2 : targetLoss (δ * (C : ℝ)) (δ * (d : ℝ)) = δ * ((C : ℝ) - (d : ℝ)) := by
    simp only [targetLoss]
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have e3 : targetLoss (δ * (C : ℝ)) 0 = δ * (C : ℝ) := by
    simp only [targetLoss]
    rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  rw [e1, e2, e3]
  have hj : (j : ℝ) = (k : ℝ) * (d : ℝ) - (q : ℝ) * (s : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hkd
    push_cast at this
    linarith
  field_simp
  rw [hj]
  ring

/-! ## Section 4: the defect spectrum at a coprime mixing weight -/

/-- **Theorem S9 (the defect spectrum is the full lattice slice).**  Let
`gcd(k, q) = 1` and let `j` be any residue `0 ≤ j < q`.  Then there is a convex
`1`-Lipschitz loss (distance to a target weight) and a pair of weights whose
`δ`-grid quantized convexity defect at mixing weight `k/q` is exactly `δ·j/q`.

So the set of achievable defects at a coprime rational mixing weight is precisely
the arithmetic progression `(δ/q)·{0, …, q−1}` allowed by the arithmetic half of
the denominator law: no value in that lattice slice is missing. -/
theorem defect_spectrum {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q)
    (hcop : Nat.Coprime k q) {j : ℤ} (hj0 : 0 ≤ j) (hjq : j < (q : ℤ)) :
    ∃ c x y : ℝ, ConvexOn ℝ univ (targetLoss c) ∧ LipschitzWith 1 (targetLoss c) ∧
      targetLoss c (gridRound δ (((k : ℝ) / q) * x + (1 - (k : ℝ) / q) * y))
        - (((k : ℝ) / q) * targetLoss c (gridRound δ x)
          + (1 - (k : ℝ) / q) * targetLoss c (gridRound δ y))
        = δ * (j : ℝ) / (q : ℝ) := by
  obtain ⟨d, e, he⟩ := exists_mul_sub_dvd hcop j
  have hkd : (k : ℤ) * d = (q : ℤ) * e + j := by linarith [he]
  set C : ℤ := max d (max e 0)
  refine ⟨δ * (C : ℝ), δ * ((d : ℝ) - 1 / 2), -(δ / 2), convexOn_targetLoss _,
    lipschitzWith_targetLoss _, ?_⟩
  exact targetLoss_defect_witness hδ hq hkd hj0 hjq (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right d _)) ((le_max_right _ _).trans (le_max_right d _))

/-- The set of convexity defects of `δ`-grid quantized landscapes of convex
`1`-Lipschitz losses, at the fixed mixing weight `a = k/q`. -/
-- [dropped: platform already declares defectSet]
theorem denominator_constant_exact {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hq : 0 < q) (hk : k ≤ q)
    (hcop : Nat.Coprime k q) :
    IsGreatest (defectSet δ k q) (δ * (1 - 1 / (q : ℝ))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · -- attainment at `j = q − 1`
    have hj0 : (0 : ℤ) ≤ (q : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      linarith
    have hjq : (q : ℤ) - 1 < (q : ℤ) := by linarith
    obtain ⟨c, x, y, hconv, hlip, heq⟩ := defect_spectrum hδ hq hcop hj0 hjq
    refine ⟨targetLoss c, x, y, hconv, hlip, ?_⟩
    rw [heq]
    have : (((q : ℤ) - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
    rw [this]
    field_simp
  · rintro D ⟨f, x, y, hconv, hlip, rfl⟩
    have h := gridRound_defect_denominator (L := 1) hconv hlip hδ hq hk x y
    have hone : ((1 : NNReal) : ℝ) = 1 := by norm_num
    rw [hone, one_mul] at h
    linarith

/-! ## Section 5: general (non-reduced) mixing weights -/

/-- **Theorem S11 (only the reduced denominator matters).**  For an arbitrary
mixing weight `k/q` with `0 < k < q`, the exact maximal convexity defect is
`(1 − g/q)·δ` where `g = gcd(k, q)`: the sharp constant depends on the *reduced*
denominator `q/g` alone.  Two mixing weights of the same value have the same
convexity cost, and a weight with a small reduced denominator (e.g. `1/2`) is
strictly gentler than a nearby weight with a large one. -/
theorem denominator_constant_reduced {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q) :
    IsGreatest (defectSet δ k q) (δ * (1 - (Nat.gcd k q : ℝ) / (q : ℝ))) := by
  have hq0 : 0 < q := lt_trans hk0 hkq
  set g : ℕ := Nat.gcd k q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hk0
  obtain ⟨k', hk'⟩ : g ∣ k := Nat.gcd_dvd_left k q
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_right k q
  have hq'0 : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · simp [h] at hq'; omega
    · exact h
  have hk'0 : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h | h
    · simp [h] at hk'; omega
    · exact h
  have hcop : Nat.Coprime k' q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := k) (n := q) hg0
    have e1 : k / g = k' := by rw [hk']; exact Nat.mul_div_cancel_left _ hg0
    have e2 : q / g = q' := by rw [hq']; exact Nat.mul_div_cancel_left _ hg0
    rwa [e1, e2] at this
  have hk'q' : k' ≤ q' := by
    have : g * k' < g * q' := by rw [← hk', ← hq']; exact hkq
    exact le_of_lt (lt_of_mul_lt_mul_left this (Nat.zero_le g))
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'0
  -- the two fractions agree as real numbers
  have hfrac : ((k : ℝ) / (q : ℝ)) = ((k' : ℝ) / (q' : ℝ)) := by
    rw [hk', hq']
    push_cast
    field_simp
  have hbound : δ * (1 - (g : ℝ) / (q : ℝ)) = δ * (1 - 1 / (q' : ℝ)) := by
    rw [hq']
    push_cast
    field_simp
  have hset : defectSet δ k q = defectSet δ k' q' := by
    unfold defectSet
    rw [hfrac]
  rw [hset, hbound]
  exact denominator_constant_exact hδ hq'0 hk'q' hcop

/-! ## Section 6: the denominator law for whole weight tensors -/

section Tensor

variable {ι : Type*} [Fintype ι] {L : NNReal} {f : (ι → ℝ) → ℝ}

/-- Entrywise discrepancy bound: quantizing a rational convex combination of two
weight tensors differs from the same combination of the quantized tensors by at
most `(1 − 1/q)·δ` in sup norm. -/
lemma quantizeTensor_denominator_dist {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q)
    (W V : ι → ℝ) :
    ‖quantizeTensor δ (((k : ℝ) / q) • W + (1 - (k : ℝ) / q) • V)
      - (((k : ℝ) / q) • quantizeTensor δ W + (1 - (k : ℝ) / q) • quantizeTensor δ V)‖
      ≤ δ * (1 - 1 / (q : ℝ)) := by
  have hq0 : 0 < q := lt_trans hk0 hkq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq1 : 1 / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast hq0
  refine (pi_norm_le_iff_of_nonneg (by nlinarith)).2 fun i => ?_
  have hi : (((k : ℝ) / q) • W + (1 - (k : ℝ) / q) • V) i
      = ((k : ℝ) / q) * W i + (1 - (k : ℝ) / q) * V i := rfl
  have e : (quantizeTensor δ (((k : ℝ) / q) • W + (1 - (k : ℝ) / q) • V)
      - (((k : ℝ) / q) • quantizeTensor δ W + (1 - (k : ℝ) / q) • quantizeTensor δ V)) i
      = -(((k : ℝ) / q) * gridRound δ (W i) + (1 - (k : ℝ) / q) * gridRound δ (V i)
          - gridRound δ (((k : ℝ) / q) * W i + (1 - (k : ℝ) / q) * V i)) := by
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, quantizeTensor, hi]
    ring
  rw [Real.norm_eq_abs, e, abs_neg]
  exact discrepancy_le_denominator hδ hk0 hkq (W i) (V i)

/-- **Theorem S12 (tensor denominator law).**  For a convex `L`-Lipschitz loss on
whole transformer weight tensors, entrywise `δ`-grid quantization satisfies the
convexity inequality at any mixing weight `k/q` with defect at most
`(1 − 1/q)·L·δ`.  Interpolating two quantized checkpoints with a low-denominator
weight (e.g. a `1/2` model soup) is provably gentler on the landscape than an
arbitrary interpolation, and by `denominator_constant_reduced` the constant
cannot be improved. -/
theorem quantizeTensor_defect_denominator (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    {δ : ℝ} (hδ : 0 < δ) {k q : ℕ} (hk0 : 0 < k) (hkq : k < q) (W V : ι → ℝ) :
    f (quantizeTensor δ (((k : ℝ) / q) • W + (1 - (k : ℝ) / q) • V))
      ≤ ((k : ℝ) / q) * f (quantizeTensor δ W)
        + (1 - (k : ℝ) / q) * f (quantizeTensor δ V) + (L : ℝ) * (δ * (1 - 1 / (q : ℝ))) := by
  have hq0 : 0 < q := lt_trans hk0 hkq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have ha0 : (0 : ℝ) ≤ (k : ℝ) / q := by positivity
  have ha1 : (k : ℝ) / q ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast hkq.le
  set A : ι → ℝ := quantizeTensor δ (((k : ℝ) / q) • W + (1 - (k : ℝ) / q) • V)
  set B : ι → ℝ := ((k : ℝ) / q) • quantizeTensor δ W
    + (1 - (k : ℝ) / q) • quantizeTensor δ V
  have hdist : ‖A - B‖ ≤ δ * (1 - 1 / (q : ℝ)) :=
    quantizeTensor_denominator_dist hδ hk0 hkq W V
  have hlip : |f A - f B| ≤ (L : ℝ) * ‖A - B‖ := abs_sub_le_lipschitz hL A B
  have hmul : (L : ℝ) * ‖A - B‖ ≤ (L : ℝ) * (δ * (1 - 1 / (q : ℝ))) :=
    mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  have hAB : f A ≤ f B + (L : ℝ) * (δ * (1 - 1 / (q : ℝ))) := by
    have := (abs_le.1 (hlip.trans hmul)).2
    linarith
  have hconv : f B ≤ ((k : ℝ) / q) * f (quantizeTensor δ W)
      + (1 - (k : ℝ) / q) * f (quantizeTensor δ V) :=
    hf.2 (mem_univ _) (mem_univ _) ha0 (by linarith) (by ring)
  linarith

end Tensor

/-! ## Section 7: a spectral converse — the defect set is an arithmetic fingerprint

The exact constants of Sections 4–5 can be read backwards: the convexity defects
of the quantized landscape are an *observable* of a training run (one measures the
violation of the convexity inequality), and they determine the arithmetic data of
the quantizer. -/

/-- **Theorem S13 (the mesh is determined by the defects).**  Two grid quantizers
with the same set of achievable convexity defects at one coprime mixing weight
have the same mesh.  The convexity defect spectrum of a quantized landscape
therefore *identifies* the lattice it was produced by. -/
theorem mesh_determined_by_defectSet {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') {k q : ℕ}
    (hq : 1 < q) (hk : k ≤ q) (hcop : Nat.Coprime k q)
    (h : defectSet δ k q = defectSet δ' k q) : δ = δ' := by
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 := denominator_constant_exact hδ hq0 hk hcop
  have h2 := denominator_constant_exact hδ' hq0 hk hcop
  rw [h] at h1
  have hmax : δ * (1 - 1 / (q : ℝ)) = δ' * (1 - 1 / (q : ℝ)) := h1.unique h2
  have hpos : 0 < 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]
      exact hqR
    linarith
  exact mul_right_cancel₀ (ne_of_gt hpos) hmax

/-- **Theorem S14 (the reduced denominator is determined by the defects).**  At a
fixed mesh, two mixing weights with the same defect set have the same *reduced*
denominator.  Combined with `denominator_constant_reduced` this says that the
reduced denominator of the interpolation weight is a complete invariant of the
convexity cost: it can be recovered from landscape measurements alone. -/
theorem reducedDenominator_determined_by_defectSet {δ : ℝ} (hδ : 0 < δ) {k q k' q' : ℕ}
    (hk0 : 0 < k) (hkq : k < q) (hk0' : 0 < k') (hkq' : k' < q')
    (h : defectSet δ k q = defectSet δ k' q') :
    q / Nat.gcd k q = q' / Nat.gcd k' q' := by
  have hq0 : 0 < q := lt_trans hk0 hkq
  have hq0' : 0 < q' := lt_trans hk0' hkq'
  have hg0 : 0 < Nat.gcd k q := Nat.gcd_pos_of_pos_left _ hk0
  have hg0' : 0 < Nat.gcd k' q' := Nat.gcd_pos_of_pos_left _ hk0'
  have hgd : Nat.gcd k q ∣ q := Nat.gcd_dvd_right k q
  have hgd' : Nat.gcd k' q' ∣ q' := Nat.gcd_dvd_right k' q'
  have h1 := denominator_constant_reduced hδ hk0 hkq
  have h2 := denominator_constant_reduced hδ hk0' hkq'
  rw [h] at h1
  have hmax : δ * (1 - (Nat.gcd k q : ℝ) / (q : ℝ))
      = δ * (1 - (Nat.gcd k' q' : ℝ) / (q' : ℝ)) := h1.unique h2
  have hfrac : (Nat.gcd k q : ℝ) / (q : ℝ) = (Nat.gcd k' q' : ℝ) / (q' : ℝ) := by
    have := mul_left_cancel₀ (ne_of_gt hδ) hmax
    linarith
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqR' : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq0'
  have hgR : (0 : ℝ) < (Nat.gcd k q : ℝ) := by exact_mod_cast hg0
  have hgR' : (0 : ℝ) < (Nat.gcd k' q' : ℝ) := by exact_mod_cast hg0'
  have hcast : ((q / Nat.gcd k q : ℕ) : ℝ) = ((q' / Nat.gcd k' q' : ℕ) : ℝ) := by
    rw [Nat.cast_div hgd (ne_of_gt hgR), Nat.cast_div hgd' (ne_of_gt hgR')]
    rw [div_eq_div_iff (ne_of_gt hqR) (ne_of_gt hqR')] at hfrac
    rw [div_eq_div_iff (ne_of_gt hgR) (ne_of_gt hgR')]
    linarith
  exact_mod_cast hcast

end QuantizedWeightLattices.DenominatorSharp
section
open QuantizedWeightLattices.DenominatorSharp
open Set QuantizedWeightLattices QuantizedWeightLattices.SharpConstant
variable {ι : Type*} [Fintype ι] {L : NNReal} {f : (ι → ℝ) → ℝ}

theorem solution {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') {k q : ℕ}
    (hq : 1 < q) (hk : k ≤ q) (hcop : Nat.Coprime k q)
    (h : defectSet δ k q = defectSet δ' k q) :
    δ = δ' := by
  first
  | exact QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet hδ hδ' hq hk hcop h
  | exact QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet
  | exact @QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet _ hδ hδ' k q hq hk hcop h
  | apply QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet
  | exact QuantizedWeightLattices.DenominatorSharp.mesh_determined_by_defectSet ..


end
