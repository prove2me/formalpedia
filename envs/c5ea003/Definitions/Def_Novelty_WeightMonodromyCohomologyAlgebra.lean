-- Prove2me | Definitions.Def_Novelty_WeightMonodromyCohomologyAlgebra
-- name    : Novelty_WeightMonodromyCohomologyAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:53:52.830647+00:00
-- url     : https://prove2.me/theorems/ea4dbfee-5870-486a-868c-9ada650f26f2
-- title:
--   Aether Catalog definitions — Novelty_WeightMonodromyCohomologyAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.WeightMonodromyCohomologyAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/WeightMonodromyCohomologyAlgebra.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# The cohomology algebra of a weight-graded dg-algebra, and its strict diagonal model

Companion to `Catalog/Novelty/WeightMonodromyFormality.lean`.

The first part sets up the multiplicative structure of cohomology for a `WeightedDGA`:
cocycles form a subalgebra and coboundaries a two-sided ideal in it, so that `H = Z / B` is a
`k`-algebra.  Note that the Leibniz rule is only postulated for *bihomogeneous* elements, so
these statements genuinely require the bigraded decomposition (they are proved componentwise).

The second part upgrades formality to its sharpest strict form under purity: the *diagonal*
cocycles (bidegree `(n, n)`, i.e. weight = degree, the shape produced by weight-monodromy)
form a subalgebra `diagAlg` on which the differential vanishes identically and which surjects
onto the cohomology algebra.  Consequently the cohomology algebra of `A` is the quotient of an
honest subalgebra of `A` with zero differential — a *strict multiplicative lift* of `H`.
-/

namespace WeightMonodromy

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] (D : WeightedDGA 𝒜)

/-! ### Cocycles form a subalgebra, coboundaries a two-sided ideal -/

/-- The product of two cocycles is a cocycle. -/
theorem d_mul_eq_zero {a b : A} (ha : D.d a = 0) (hb : D.d b = 0) : D.d (a * b) = 0 := by
  have ha' : a = ∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a := (sum_cmpL 𝒜 a).symm
  calc D.d (a * b) = D.d ((∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a) * b) := by rw [← ha']
    _ = ∑ i ∈ supp 𝒜 a, D.d (cmpL 𝒜 i a * b) := by rw [Finset.sum_mul, map_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [D.leibniz i.1 i.2 _ b (by simpa using cmpL_mem 𝒜 a i), D.cmpL_cocycle ha i, hb]
        simp



/-! ### The diagonal subalgebra of pure cocycles -/

/-- The algebra of *diagonal* cocycles: bihomogeneous cocycles whose weight equals their
cohomological degree.  This is the shape of cohomology classes predicted by the
weight-monodromy conjecture. -/
noncomputable def diagAlg : Submodule k A := ⨆ n : ℤ, (𝒜 (n, n) ⊓ LinearMap.ker D.d)

lemma diagAlg_le_ker : diagAlg D ≤ LinearMap.ker D.d :=
  iSup_le fun _ => inf_le_right

/-- The differential vanishes identically on the diagonal subalgebra. -/
lemma d_eq_zero_of_mem_diagAlg {a : A} (ha : a ∈ diagAlg D) : D.d a = 0 :=
  diagAlg_le_ker D ha

lemma mem_diagAlg {n : ℤ} {a : A} (ha : a ∈ 𝒜 (n, n)) (hd : D.d a = 0) : a ∈ diagAlg D :=
  le_iSup (fun n : ℤ => 𝒜 (n, n) ⊓ LinearMap.ker D.d) n ⟨ha, by simpa using hd⟩

lemma one_mem_diagAlg : (1 : A) ∈ diagAlg D :=
  mem_diagAlg D (n := 0) (by simpa using SetLike.one_mem_graded 𝒜) D.d_one

/-- The diagonal cocycles form a subalgebra. -/
lemma diagAlg_mul_mem {a b : A} (ha : a ∈ diagAlg D) (hb : b ∈ diagAlg D) :
    a * b ∈ diagAlg D := by
  have hle : diagAlg D * diagAlg D ≤ diagAlg D := by
    unfold diagAlg
    rw [Submodule.iSup_mul]
    refine iSup_le fun n => ?_
    rw [Submodule.mul_iSup]
    refine iSup_le fun m => Submodule.mul_le.mpr fun x hx y hy => ?_
    have hxy : x * y ∈ 𝒜 (n + m, n + m) := by
      have := SetLike.mul_mem_graded hx.1 hy.1
      simpa [Prod.mk_add_mk] using this
    refine mem_diagAlg D hxy (d_mul_eq_zero D ?_ ?_)
    · simpa using hx.2
    · simpa using hy.2
  exact hle (Submodule.mul_mem_mul ha hb)

/-- Data exhibiting a *strict multiplicative lift* of the cohomology algebra: a subalgebra of
`A` on which the differential vanishes and which hits every cohomology class.  The cohomology
algebra of `A` is then the quotient of `sec` by the ideal `sec ∩ im d` (see
`StrictSectionData.kernel_mul_mem` and `StrictSectionData.mul_kernel_mem`). -/
structure StrictSectionData (D : WeightedDGA 𝒜) where
  /-- The lifting subalgebra. -/
  sec : Submodule k A
  one_mem : (1 : A) ∈ sec
  mul_mem : ∀ a ∈ sec, ∀ b ∈ sec, a * b ∈ sec
  /-- The differential vanishes identically on `sec`. -/
  d_zero : ∀ a ∈ sec, D.d a = 0
  /-- Every cohomology class of `A` is represented in `sec`. -/
  surj : ∀ a, D.d a = 0 → ∃ z ∈ sec, ∃ c, a = z + D.d c

namespace StrictSectionData

variable {D}



end StrictSectionData

/-- **Strict formality under purity.**  If the weight grading is pure, the diagonal cocycles
form a subalgebra with zero differential which surjects onto the cohomology algebra: the
cohomology algebra of `A` is realised as an honest subquotient of `A` with zero differential.

This is the sharpest strict form of the formality statement for spaces satisfying the
weight-monodromy conjecture. -/
noncomputable def diagonal_strict_section (hpure : IsWeightPure D) : StrictSectionData D where
  sec := diagAlg D
  one_mem := one_mem_diagAlg D
  mul_mem := fun _ ha _ hb => diagAlg_mul_mem D ha hb
  d_zero := fun _ ha => d_eq_zero_of_mem_diagAlg D ha
  surj := by
    intro a ha
    classical
    set s := supp 𝒜 a with hs
    set z := ∑ i ∈ s.filter (fun i => i.1 = i.2), cmpL 𝒜 i a with hz
    have hsplit : a = z + ∑ i ∈ s.filter (fun i => ¬ i.1 = i.2), cmpL 𝒜 i a := by
      rw [hz, Finset.sum_filter_add_sum_filter_not]
      exact (sum_cmpL 𝒜 a).symm
    have hzmem : z ∈ diagAlg D := by
      refine Submodule.sum_mem _ fun i hi => ?_
      have hdiag : i.1 = i.2 := (Finset.mem_filter.mp hi).2
      refine mem_diagAlg D (n := i.1) ?_ (D.cmpL_cocycle ha i)
      have := cmpL_mem 𝒜 a i
      rwa [show (i.1, i.1) = i from Prod.ext rfl hdiag]
    obtain ⟨c, -, hc⟩ : ∃ c ∈ (⊤ : Submodule k A), D.d c
        = ∑ i ∈ s.filter (fun i => ¬ i.1 = i.2), cmpL 𝒜 i a := by
      refine exists_primitive_sum D fun i hi => ?_
      have hne : i.1 ≠ i.2 := (Finset.mem_filter.mp hi).2
      obtain ⟨c, -, hc⟩ := hpure i.1 i.2 hne (cmpL 𝒜 i a)
        (by simpa using cmpL_mem 𝒜 a i) (D.cmpL_cocycle ha i)
      exact ⟨c, Submodule.mem_top, hc⟩
    exact ⟨z, hzmem, c, by rw [hc]; exact hsplit⟩


/-! ### Subalgebra packaging -/

/-- The cocycles of a weight-graded dg-algebra form a `k`-subalgebra. -/
noncomputable def cocycleAlg : Subalgebra k A where
  carrier := {a | D.d a = 0}
  mul_mem' := fun ha hb => d_mul_eq_zero D ha hb
  add_mem' := fun ha hb => by
    show D.d _ = 0
    rw [map_add, show D.d _ = 0 from ha, show D.d _ = 0 from hb, add_zero]
  zero_mem' := by simp
  one_mem' := D.d_one
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq, Algebra.algebraMap_eq_smul_one, map_smul, D.d_one, smul_zero]

/-- The diagonal cocycles form a `k`-subalgebra of `A`, on which the differential vanishes. -/
noncomputable def diagSubalg : Subalgebra k A where
  carrier := (diagAlg D : Set A)
  mul_mem' := fun ha hb => diagAlg_mul_mem D ha hb
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  one_mem' := one_mem_diagAlg D
  algebraMap_mem' := fun r => by
    have : algebraMap k A r = r • (1 : A) := Algebra.algebraMap_eq_smul_one r
    rw [this]
    exact Submodule.smul_mem _ _ (one_mem_diagAlg D)



end WeightMonodromy


