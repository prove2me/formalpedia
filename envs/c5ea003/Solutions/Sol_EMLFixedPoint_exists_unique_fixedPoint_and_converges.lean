-- Prove2me | solution 1 for EMLFixedPoint.exists_unique_fixedPoint_and_converges
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:14.463739+00:00
-- url     : https://prove2.me/submissions/8760d6c8-49cd-4c98-ae32-6c9650bc5aaf

-- Sol generated from Applications/EML/FixedPointIteration.lean
import Mathlib
import Definitions.Def_Applications_EML_FixedPointIteration
import Theorems.Thm_EMLFixedPoint_lipschitzOn_emlMap_Icc

/-!
# Fixed points of an exponential--logarithmic iteration

This file studies `x ↦ exp a * log (x + c)`.  The unrestricted test claim from
this research question is false: even with `0 < a < 1` and `0 < c < 1`, a fixed
point need not exist.  We prove this for `a = log 2`, `c = 1/2` on the natural
logarithmic domain.

The positive result is the precise contraction theorem suggested by the question.
On a closed invariant interval `[L,U]`, if `L+c>0` and
`exp a / (L+c) ≤ q < 1`, the map has a unique fixed point in the interval;
every iteration starting there converges to it with Banach's geometric error bound.
-/

noncomputable section

open Real Set Filter Function Topology

open EMLFixedPoint





/-- Under the explicit derivative bound, the restricted map is a contraction. -/
theorem contracting_restrictedMap {a c L U q : ℝ}
    (hpos : 0 < L + c) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hderiv : Real.exp a / (L + c) ≤ q)
    (hmap : MapsTo (emlMap a c) (Icc L U) (Icc L U)) :
    ContractingWith ⟨q, hq0⟩ (restrictedMap hmap) := by
  have hLip : LipschitzOnWith ⟨q, hq0⟩ (emlMap a c) (Icc L U) :=
    lipschitzOn_emlMap_Icc hpos hq0 hderiv
  refine ⟨?_, ?_⟩
  · exact_mod_cast hq1
  · intro x y
    exact hLip x.2 y.2






open EMLFixedPoint in
theorem solution    {a c L U q : ℝ} (hpos : 0 < L + c)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hderiv : Real.exp a / (L + c) ≤ q)
    (hmap : MapsTo (emlMap a c) (Icc L U) (Icc L U)) (x₀ : ℝ) (hx₀ : x₀ ∈ Icc L U) :
    ∃ xstar ∈ Icc L U,
      emlMap a c xstar = xstar ∧
      (∀ y ∈ Icc L U, emlMap a c y = y → y = xstar) ∧
      Tendsto (fun n => (emlMap a c)^[n] x₀) atTop (𝓝 xstar) ∧
      ∀ n : ℕ, dist ((emlMap a c)^[n] x₀) xstar ≤
        dist x₀ (emlMap a c x₀) * q ^ n / (1 - q) := by
  let F := hmap.restrict (emlMap a c) (Icc L U) (Icc L U)
  let X : Icc L U := ⟨x₀, hx₀⟩
  letI : Nonempty (Icc L U) := ⟨X⟩
  have hcontract := contracting_restrictedMap hpos hq0 hq1 hderiv hmap
  let Xstar := ContractingWith.fixedPoint F hcontract
  have hfix : F Xstar = Xstar := hcontract.fixedPoint_isFixedPt
  have hit (n : ℕ) : ((F^[n]) X).1 = ((emlMap a c)^[n]) x₀ := by
    rw [show F = hmap.restrict (emlMap a c) (Icc L U) (Icc L U) from rfl,
      MapsTo.iterate_restrict]
    rfl
  refine ⟨Xstar, Xstar.2, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hfix
  · intro y hy hyfix
    let Y : Icc L U := ⟨y, hy⟩
    have hY : F Y = Y := Subtype.ext hyfix
    exact congrArg Subtype.val (hcontract.fixedPoint_unique' hY hfix)
  · have ht := hcontract.tendsto_iterate_fixedPoint X
    have hv := continuous_subtype_val.continuousAt.tendsto.comp ht
    convert hv using 1
    funext n
    exact (hit n).symm
  · intro n
    have hb := hcontract.apriori_dist_iterate_fixedPoint_le X n
    rw [← hit n]
    exact hb
