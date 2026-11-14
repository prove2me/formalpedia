-- Prove2me | solution 2 for KServer.antipodal_coalesced_growth_sum_sharp
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T01:58:03.095819+00:00
-- url     : https://prove2.me/submissions/80c66e1b-b8b6-4187-ac8d-3550da53d0c9

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServer_model
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

set_option autoImplicit false

-- Source: field/KServerField.lean
section SharpFile000
namespace KServerConj

abbrev Var (k : ℕ) (M : Type*) := (Fin k × M) ⊕ (ℕ × M)
abbrev F (k : ℕ) (M : Type*) := FractionRing (MvPolynomial (Var k M) ℚ)
abbrev K (k : ℕ) (M : Type*) := HahnSeries ℝ (F k M)

noncomputable abbrev nu {k : ℕ} {M : Type*} (f : K k M) : WithTop ℝ :=
  HahnSeries.addVal ℝ (F k M) f

noncomputable abbrev zp {k : ℕ} {M : Type*} (a : ℝ) : K k M :=
  HahnSeries.single a (1 : F k M)

noncomputable abbrev varF {k : ℕ} {M : Type*} (v : Var k M) : F k M :=
  algebraMap (MvPolynomial (Var k M) ℚ) (F k M) (MvPolynomial.X v)

noncomputable abbrev coef {k : ℕ} {M : Type*} (v : Var k M) : K k M :=
  HahnSeries.C (varF v)

def FreeOf {k : ℕ} {M : Type*} (S : Set (Var k M)) (f : K k M) : Prop :=
  ∀ a : ℝ, f.coeff a ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)

end KServerConj
end SharpFile000

-- Source: Definitions/Def_KServerConj_symProd.lean
section SharpFile001
namespace KServerConj

def symProd {R : Type*} [CommRing R] {k : ℕ} (a b : Fin k → R) : Sym2 (Fin k) → R :=
  Sym2.lift ⟨fun i j => if i = j then a i * b i else a i * b j + a j * b i, by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp only [h, Ne.symm h, if_false]; ring⟩

theorem symProd_comm {R : Type*} [CommRing R] {k : ℕ} (a b : Fin k → R) :
    symProd a b = symProd b a := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [symProd, Sym2.lift_mk]
    split_ifs with h
    · subst h; ring
    · ring

def sym2Mat {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    Matrix (Sym2 (Fin k)) (Sym2 (Fin k)) R :=
  fun p c => Sym2.lift ⟨fun i j => symProd (fun l => A l i) (fun l => A l j) p, by
    intro i j
    exact congrFun (symProd_comm _ _) p⟩ c

end KServerConj
end SharpFile001

-- Source: Definitions/Def_KServerConj_minorVal.lean
section SharpFile002
namespace KServerConj

noncomputable def minorVal {F : Type*} [Field F] {R ι : Type*} [Fintype R] [Fintype ι]
    (G : Matrix R ι (HahnSeries ℝ F)) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : R ↪ ι => HahnSeries.addVal ℝ F (G.submatrix id e).det

end KServerConj
end SharpFile002

-- Source: Definitions/Def_KServerConj_Psi.lean
section SharpFile003
namespace KServerConj

noncomputable def Qmat {k : ℕ} {M : Type*} [PseudoMetricSpace M] (q : M → Fin k → K k M) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (K k M) :=
  fun p c => Sym2.lift ⟨fun x y => zp (-dist x y) * symProd (q x) (q y) p, by
    intro x y
    dsimp only
    rw [dist_comm, symProd_comm]⟩ c

noncomputable def Psi {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → K k M) : WithTop ℝ :=
  minorVal (Qmat q)

end KServerConj
end SharpFile003

-- Source: DetUpdateCol.lean
section SharpFile004
open scoped BigOperators

theorem det_mul_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (j : ι) (v : ι → R) :
    A.det * (B.updateCol j v).det =
      ∑ i, (A.updateCol i v).det *
        (B.updateCol j (fun r => A r i)).det := by
  have h : A.det • v =
      ∑ i, (A.updateCol i v).det • (fun r => A r i) := by
    rw [← Matrix.mulVec_cramer A v]
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.cramer_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h' := congrArg (fun w : ι → R => B.cramer w j) h
  simp only [map_smul, map_sum] at h'
  simpa only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cramer_apply] using h'
end SharpFile004

-- Source: ProjectedMinor.lean
section SharpFile005
open scoped BigOperators

namespace DetValuationMilestone

def prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn v W).updateCol 0 w = prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [prependColumn, Matrix.updateCol]

theorem det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (prependColumn (fun r => A r i) W).det := by
  simpa only [updateCol_prepend] using det_mul_det_updateCol A (prependColumn v W) 0 v

theorem det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (c • v) W).det = c * (prependColumn v W).det := by
  simpa only [updateCol_prepend] using Matrix.det_updateCol_smul (prependColumn v W) 0 c v

theorem prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, det_prepend_smul, mul_assoc] using
      det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)

theorem exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det = ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i * H 0 (x i) := by
  have hentry : ∀ r i, A r i = c i * H r (x i) :=
    fun r i => congrFun (hcol i) r
  simpa [Matrix.mulVec, dotProduct, Matrix.cramer_apply, hentry,
    mul_comm, mul_left_comm, mul_assoc] using
      (congrFun (Matrix.mulVec_cramer A (Pi.single 0 1)) 0).symm

theorem exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using det_eq_sum_scaled_cramer A H x c hcol)

end DetValuationMilestone
end SharpFile005

-- Source: ValuationMilestone.lean
section SharpFile006
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_sum_lower_bound
    {R ι : Type*} [AddCommMonoid R]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (s : Finset ι) (f : ι → R) (c : WithTop ℝ)
    (hf : ∀ i ∈ s, c ≤ ν (f i)) :
    c ≤ ν (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).trans (hadd _ _)

theorem valuation_lower_bound_of_minor_identity
    {R ι : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D P : R) (a M : ι → R) (δ α μ : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : D * P = ∑ i, a i * M i)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i, (μ : WithTop ℝ) ≤ ν (M i)) :
    ((α + μ - δ : ℝ) : WithTop ℝ) ≤ ν P := by
  have hsum : ((α + μ : ℝ) : WithTop ℝ) ≤ ν (∑ i, a i * M i) := by
    apply valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

theorem minValue_growth_of_minor_identities
    {R ι κ : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (M : ι → κ → R)
    (δ α μ μhat : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i y, (μ : WithTop ℝ) ≤ ν (M i y))
    (hmin : ∃ y, ν (P y) = (μhat : WithTop ℝ)) :
    α - δ ≤ μhat - μ := by
  obtain ⟨y, hy⟩ := hmin
  have h := valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

theorem exists_real_minimum_of_nonzero
    {R ι : Type*} [Zero R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (f : ι → R) (hnonzero : ∃ i, f i ≠ 0) :
    ∃ μ : ℝ,
      (Finset.univ.inf fun i => ν (f i)) = (μ : WithTop ℝ) ∧
      (∀ i, (μ : WithTop ℝ) ≤ ν (f i)) ∧
      (∃ i, ν (f i) = (μ : WithTop ℝ) ∧ f i ≠ 0) := by
  classical
  obtain ⟨i, hi⟩ := hnonzero
  have hfinite : (Finset.univ.inf fun i => ν (f i)) ≠ ⊤ := by
    exact ne_of_lt ((Finset.inf_le (Finset.mem_univ i)).trans_lt
      (lt_top_iff_ne_top.mpr fun h => hi ((htop _).mp h)))
  obtain ⟨μ, hμ⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset ι)
    ⟨i, Finset.mem_univ i⟩ (fun j => ν (f j))
  exact ⟨μ, hμ.symm, fun j => hμ.trans_le (Finset.inf_le (Finset.mem_univ j)),
    j, hj.symm.trans hμ.symm, fun hz => hfinite (hj.trans ((htop _).mpr hz))⟩

theorem canonical_minValue_growth
    {R ι κ η : Type*} [Semiring R] [Fintype ι] [Fintype κ] [Fintype η]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (F : η → R) (M : ι → κ → R)
    (hD : D ≠ 0)
    (ha_nonzero : ∃ i, a i ≠ 0)
    (hP_nonzero : ∃ y, P y ≠ 0)
    (hF_nonzero : ∃ z, F z ≠ 0)
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (hM : ∀ i y, M i y = 0 ∨ ∃ z, M i y = F z) :
    ∃ δ α μ μhat : ℝ,
      ν D = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν (a i)) = (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z => ν (F z)) = (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y => ν (P y)) = (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (fun h => hD ((htop _).mp h))
  obtain ⟨α, hα, ha, _⟩ := exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
      D a P M δ α μ μhat hδ.symm hid ha
      (fun i y => (hM i y).elim
        (fun hz => by simp [hz, (htop 0).mpr rfl])
        (fun ⟨z, hz⟩ => by simpa only [hz] using hF z))
      ⟨y, hy⟩⟩

end DetValuationMilestone
end SharpFile006

-- Source: ProjectedValuation.lean
section SharpFile007
open scoped BigOperators

namespace DetValuationMilestone

theorem canonical_projected_minValue_growth
    {n : ℕ} {R ι : Type*} [CommRing R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ δ α μ μhat : ℝ,
      ν A.det = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν ((A.updateCol i (Pi.single 0 1)).det * c i)) =
        (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z : Fin (n + 1) → ι => ν (H.submatrix id z).det) =
        (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y : Fin n → ι => ν (H.submatrix Fin.succ y).det) =
        (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  exact canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (exists_nonzero_scaled_cramer A H x c hcol hdet)
    (exists_nonzero_projected_minor H x (nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone
end SharpFile007

-- Source: MinorValuation.lean
section SharpFile008
open scoped BigOperators

namespace DetValuationMilestone

noncomputable def tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : embeddingMinorVal ν G ≤ ⊤))

theorem tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    tupleMinorVal ν G = embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => embeddingMinorVal_le_tuple ν hzero G x)

theorem add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    tupleMinorVal ν (A * G) = ν A.det + tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [tupleMinorVal, hval] using
    (add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    embeddingMinorVal ν (A * G) = ν A.det + embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using tupleMinorVal_mul ν hmul A G

end DetValuationMilestone
end SharpFile008

-- Source: HahnMinorValuation.lean
section SharpFile009
namespace KServerConj

theorem minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.embeddingMinorVal
  rfl

theorem minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj
end SharpFile009

-- Source: QuadraticMatrix.lean
section SharpFile010
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = quadraticMatrix q := rfl

noncomputable def weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end SharpFile010

-- Source: SymmetricSquare.lean
section SharpFile011
open scoped BigOperators

namespace KServerConj

@[simp] theorem symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, symProd_apply]
    split_ifs <;> ring

theorem symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using symProd_add_left b c a

theorem symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using symProd_smul_left c b a

def symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := symProd_add_right a
      map_smul' c b := symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => symProd_smul_left c a b

@[simp] theorem symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [symProd_apply, Pi.single_apply]

@[simp] theorem sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [symProdBilin, symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [symProd_single_single, Matrix.one_mulVec] using
      sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← symProd_single_single, ← Matrix.mulVec_mulVec, sym2Mat_mulVec_symProd]

end KServerConj
end SharpFile011

-- Source: SymmetricSquareBlocks.lean
section SharpFile012
namespace KServerConj

def sym2FinSuccEmbed (n : ℕ) :
    Fin (n + 1) ⊕ Sym2 (Fin n) → Sym2 (Fin (n + 1))
  | Sum.inl i => s(0, i)
  | Sum.inr p => p.map Fin.succ

theorem sym2FinSucc_top_ne_bottom (n : ℕ) (i : Fin (n + 1)) (p : Sym2 (Fin n)) :
    s((0 : Fin (n + 1)), i) ≠ p.map Fin.succ := by
  induction p using Sym2.ind with
  | _ a b =>
    simp [(Fin.succ_ne_zero a).symm, (Fin.succ_ne_zero b).symm]

theorem sym2FinSuccEmbed_injective (n : ℕ) : Function.Injective (sym2FinSuccEmbed n) := by
  intro x y h
  rcases x with i | p <;> rcases y with j | q
  · exact congrArg Sum.inl ((Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1))
  · exact False.elim (sym2FinSucc_top_ne_bottom n i q h)
  · exact False.elim (sym2FinSucc_top_ne_bottom n j p h.symm)
  · exact congrArg Sum.inr (Sym2.map.injective (Fin.succ_injective n) h)

theorem sym2FinSuccEmbed_surjective (n : ℕ) : Function.Surjective (sym2FinSuccEmbed n) := by
  intro p
  induction p using Sym2.ind with
  | _ i j =>
    cases i using Fin.cases with
    | zero => exact ⟨Sum.inl j, rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact ⟨Sum.inl i.succ, Sym2.eq_swap⟩
      | succ j => exact ⟨Sum.inr s(i, j), rfl⟩

noncomputable def sym2FinSuccEquiv (n : ℕ) :
    Sym2 (Fin (n + 1)) ≃ Fin (n + 1) ⊕ Sym2 (Fin n) :=
  (Equiv.ofBijective (sym2FinSuccEmbed n)
    ⟨sym2FinSuccEmbed_injective n, sym2FinSuccEmbed_surjective n⟩).symm

@[simp] theorem sym2FinSuccEquiv_symm_inl (n : ℕ) (i : Fin (n + 1)) :
    (sym2FinSuccEquiv n).symm (Sum.inl i) = s(0, i) := rfl

@[simp] theorem sym2FinSuccEquiv_symm_inr (n : ℕ) (p : Sym2 (Fin n)) :
    (sym2FinSuccEquiv n).symm (Sum.inr p) = p.map Fin.succ := rfl

@[simp] theorem sym2FinSuccEquiv_mk_zero (n : ℕ) (i : Fin (n + 1)) :
    sym2FinSuccEquiv n s(0, i) = Sum.inl i := by
  simpa only [sym2FinSuccEquiv_symm_inl] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inl i)

@[simp] theorem sym2FinSuccEquiv_map_succ (n : ℕ) (p : Sym2 (Fin n)) :
    sym2FinSuccEquiv n (p.map Fin.succ) = Sum.inr p := by
  simpa only [sym2FinSuccEquiv_symm_inr] using
    (sym2FinSuccEquiv n).apply_symm_apply (Sum.inr p)

theorem symProd_split_top {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i)) =
      if i = 0 then a 0 * b 0 else a 0 * b i + a i * b 0 := by
  simp [symProd_apply, eq_comm]

@[simp] theorem symProd_split_top_zero {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl 0)) = a 0 * b 0 := by
  simp [symProd_apply]

theorem symProd_split_top_succ {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (i : Fin n) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inl i.succ)) =
      a 0 * b i.succ + a i.succ * b 0 := by
  simp [symProd_apply, (Fin.succ_ne_zero i).symm]

theorem symProd_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (a b : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd a b ((sym2FinSuccEquiv n).symm (Sum.inr p)) =
      symProd (fun i => a i.succ) (fun i => b i.succ) p := by
  induction p using Sym2.ind with
  | _ i j =>
    simp only [sym2FinSuccEquiv_symm_inr, Sym2.map_mk, symProd_apply,
      (Fin.succ_injective n).eq_iff]

theorem symProd_e0_split_top {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (i : Fin (n + 1)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inl i)) = h i := by
  by_cases hi : i = 0 <;> simp [hi, eq_comm]

theorem symProd_e0_split_bottom {R : Type*} [CommRing R] {n : ℕ}
    (h : Fin (n + 1) → R) (p : Sym2 (Fin n)) :
    symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm (Sum.inr p)) = 0 := by
  induction p using Sym2.ind with
  | _ i j =>
    simp [symProd_apply]

theorem symProd_e0_split {R : Type*} [CommRing R] {n : ℕ} (h : Fin (n + 1) → R) :
    (fun p : Fin (n + 1) ⊕ Sym2 (Fin n) =>
      symProd (Pi.single 0 1) h ((sym2FinSuccEquiv n).symm p)) =
      Sum.elim h (fun _ => 0) := by
  exact funext (Sum.rec (symProd_e0_split_top h) (symProd_e0_split_bottom h))

end KServerConj
end SharpFile012

-- Source: QuadraticMatrixBlocks.lean
section SharpFile013
namespace KServerConj

@[simp] theorem quadraticMatrix_apply_pair {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F)
    (p : Sym2 (Fin k)) (x y : M) :
    quadraticMatrix q p s(x, y) =
      HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p := rfl

theorem quadraticMatrix_request_column {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) :
    (quadraticMatrix q).col s(r, x) =
      symProd (Pi.single 0 1) (fun i => weightedColumns q r i x) := by
  funext p
  change HahnSeries.single (-dist r x) (1 : F) * symProd (q r) (q x) p =
    symProd (Pi.single 0 1) (HahnSeries.single (-dist r x) (1 : F) • q x) p
  rw [hqr, symProd_smul_right]
  rfl

theorem quadraticMatrix_request_top {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (i : Fin (n + 1)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inl i)) s(r, x) =
      weightedColumns q r i x := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inl i))).trans
      (symProd_e0_split_top (fun i => weightedColumns q r i x) i)

theorem quadraticMatrix_request_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : M) (p : Sym2 (Fin n)) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) s(r, x) = 0 := by
  exact (congrFun (quadraticMatrix_request_column q r hqr x)
    ((sym2FinSuccEquiv n).symm (Sum.inr p))).trans
      (symProd_e0_split_bottom (fun i => weightedColumns q r i x) p)

theorem quadraticMatrix_split_bottom {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F)
    (p : Sym2 (Fin n)) (c : Sym2 M) :
    quadraticMatrix q ((sym2FinSuccEquiv n).symm (Sum.inr p)) c =
      quadraticMatrix (fun x (i : Fin n) => q x i.succ) p c := by
  induction c using Sym2.ind with
  | _ x y =>
    exact congrArg (fun z => HahnSeries.single (-dist x y) (1 : F) * z)
      (symProd_split_bottom (q x) (q y) p)

theorem quadraticMatrix_exists_old_minor {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (x : Fin (n + 1) → M)
    (y : Sym2 (Fin n) → Sym2 M) :
    ∃ c : Sym2 (Fin (n + 1)) → Sym2 M,
      ((quadraticMatrix q).submatrix id c).det =
        ((weightedColumns q r).submatrix id x).det *
          ((quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y).det := by
  let e := sym2FinSuccEquiv n
  let c : Sym2 (Fin (n + 1)) → Sym2 M :=
    fun p => Sum.elim (fun i => s(r, x i)) y (e p)
  let A := (weightedColumns q r).submatrix id x
  let D := (quadraticMatrix (fun m (i : Fin n) => q m i.succ)).submatrix id y
  let B : Matrix (Fin (n + 1)) (Sym2 (Fin n)) (HahnSeries ℝ F) :=
    fun i j => quadraticMatrix q (e.symm (Sum.inl i)) (y j)
  have hblock : Matrix.reindex e e ((quadraticMatrix q).submatrix id c) =
      Matrix.fromBlocks A B 0 D := by
    funext u v
    rcases u with i | p <;> rcases v with j | t
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inl j))) =
        weightedColumns q r i (x j)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_top q r hqr (x j) i
    · change quadraticMatrix q (e.symm (Sum.inl i)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix q (e.symm (Sum.inl i)) (y t)
      simp only [c, e, Equiv.apply_symm_apply, Sum.elim_inr]
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inl j))) = 0
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inl] using
        quadraticMatrix_request_bottom q r hqr (x j) p
    · change quadraticMatrix q (e.symm (Sum.inr p)) (c (e.symm (Sum.inr t))) =
        quadraticMatrix (fun m (i : Fin n) => q m i.succ) p (y t)
      simpa only [c, e, Equiv.apply_symm_apply, Sum.elim_inr] using
        quadraticMatrix_split_bottom q p (y t)
  exact ⟨c, (Matrix.det_reindex_self e ((quadraticMatrix q).submatrix id c)).symm.trans
    ((congrArg Matrix.det hblock).trans (Matrix.det_fromBlocks_zero₂₁ A B D))⟩

end KServerConj
end SharpFile013

-- Source: HahnMinorTools.lean
section SharpFile014
namespace KServerConj

theorem minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩

end KServerConj
end SharpFile014

-- Source: PotentialOldBound.lean
section SharpFile015
namespace KServerConj

theorem quadraticMatrix_old_bound_finite {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) (a b : ℝ)
    (ha : minorVal (weightedColumns q r) = (a : WithTop ℝ))
    (hb : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = (b : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((a + b : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := exists_minorVal_minimizer (weightedColumns q r) a ha
  obtain ⟨y, hy⟩ := exists_minorVal_minimizer
    (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) b hb
  obtain ⟨c, hc⟩ := quadraticMatrix_exists_old_minor q r hqr x y
  have hval : HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id c).det =
      ((a + b : ℝ) : WithTop ℝ) := by
    simpa only [AddValuation.map_mul, hx, hy, WithTop.coe_add] using
      congrArg (HahnSeries.addVal ℝ F) hc
  exact (minorVal_le_tuple (quadraticMatrix q) c).trans_eq hval

theorem quadraticMatrix_old_bound {F : Type*} [Field F] {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M)
    (hqr : q r = Pi.single 0 1) :
    minorVal (quadraticMatrix q) ≤
      minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) +
        minorVal (weightedColumns q r) := by
  by_cases hH : minorVal (weightedColumns q r) = ⊤
  · simp [hH]
  by_cases hT : minorVal (quadraticMatrix (fun m (i : Fin n) => q m i.succ)) = ⊤
  · simp [hT]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hH
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hT
  simpa only [← ha, ← hb, WithTop.coe_add, add_comm] using
    quadraticMatrix_old_bound_finite q r hqr a b ha.symm hb.symm

end KServerConj
end SharpFile015

-- Source: QuadraticNewColumns.lean
section SharpFile016
open scoped BigOperators

namespace KServerConj

noncomputable def finSuccThreeBlockEquiv (m : ℕ) : Fin (m + 1) ≃ PUnit ⊕ Fin m :=
  (finSuccEquiv m).trans ((Equiv.optionEquivSumPUnit (Fin m)).trans (Equiv.sumComm _ _))

noncomputable def quadraticThreeBlockEquiv (m : ℕ) :
    Sym2 (Fin (m + 1)) ≃ PUnit ⊕ (Fin m ⊕ Sym2 (Fin m)) :=
  (sym2FinSuccEquiv m).trans
    ((Equiv.sumCongr (finSuccThreeBlockEquiv m) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

@[simp] theorem quadraticThreeBlockEquiv_symm_first (m : ℕ) (u : PUnit) :
    (quadraticThreeBlockEquiv m).symm (Sum.inl u) = s(0, 0) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_middle (m : ℕ) (i : Fin m) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inl i)) = s(0, i.succ) := by
  simp [quadraticThreeBlockEquiv, finSuccThreeBlockEquiv]

@[simp] theorem quadraticThreeBlockEquiv_symm_last (m : ℕ) (p : Sym2 (Fin m)) :
    (quadraticThreeBlockEquiv m).symm (Sum.inr (Sum.inr p)) = p.map Fin.succ := by
  simp [quadraticThreeBlockEquiv]

noncomputable def quadraticNewReference {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) :
    Matrix (PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) (PUnit ⊕ (M ⊕ Sym2 M)) (HahnSeries ℝ F) :=
  Matrix.fromBlocks 1 0 0
    (Matrix.fromBlocks ((weightedColumns q r).submatrix Fin.succ id) 0 0
      (quadraticMatrix (fun y => Fin.tail (q y))))

noncomputable def quadraticNewCoefficients {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F) (x y : M) :
    PUnit ⊕ (M ⊕ Sym2 M) → HahnSeries ℝ F :=
  Sum.elim (fun _ => HahnSeries.single (-dist x y) (1 : F) * δ x * δ y)
    (Sum.elim (fun z =>
      (Pi.single y (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) :
        M → HahnSeries ℝ F) z +
      (Pi.single x (HahnSeries.single (dist r x - dist x y) (1 : F) * δ y) :
        M → HahnSeries ℝ F) z)
      (Pi.single s(x, y) 1 : Sym2 M → HahnSeries ℝ F))

theorem single_neg_mul_sub {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (-a) (1 : F) : HahnSeries ℝ F) *
        HahnSeries.single (a - b) 1 = HahnSeries.single (-b) 1 := by
  simp [HahnSeries.single_mul_single, sub_eq_add_neg, ← add_assoc]

theorem weightedColumns_mul_shift {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin m → HahnSeries ℝ F) (r y : M)
    (i : Fin m) (b : ℝ) (a : HahnSeries ℝ F) :
    weightedColumns q r i y * (HahnSeries.single (dist r y - b) (1 : F) * a) =
      HahnSeries.single (-b) (1 : F) * a * q y i := by
  calc
    _ = (HahnSeries.single (-dist r y) (1 : F) *
        HahnSeries.single (dist r y - b) (1 : F)) * a * q y i := by
      dsimp only [weightedColumns]
      ring
    _ = _ := by rw [single_neg_mul_sub]

theorem quadraticNewColumn_expansion {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (x y : M) (i : PUnit ⊕ (Fin m ⊕ Sym2 (Fin m))) :
    quadraticMatrix (fun z => Fin.cons (δ z) (Fin.tail (q z)))
        ((quadraticThreeBlockEquiv m).symm i) s(x, y) =
      ∑ j, quadraticNewReference q r i j * quadraticNewCoefficients r δ x y j := by
  rcases i with u | (i | p)
  · simp [quadraticNewReference, quadraticNewCoefficients, mul_assoc]
  · simp [quadraticNewReference, quadraticNewCoefficients, symProd_apply, Fin.tail,
      Pi.single_apply, mul_ite, mul_add, Finset.sum_add_distrib, weightedColumns_mul_shift]
    simp only [(Fin.succ_ne_zero i).symm, if_false, mul_assoc, mul_comm, mul_left_comm]
  · induction p using Sym2.ind with
    | _ i j =>
      simp [quadraticNewReference, quadraticNewCoefficients, quadraticMatrix, symProd,
        Pi.single_apply, mul_ite, Fin.tail]

end KServerConj
end SharpFile016

-- Source: QuadraticNewValuation.lean
section SharpFile017
namespace KServerConj

theorem addVal_single_one {F : Type*} [Field F] (a : ℝ) :
    HahnSeries.addVal ℝ F (HahnSeries.single a (1 : F)) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem quadraticNew_unit_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (-dist x y) (1 : F) * δ x * δ y) := by
  rw [AddValuation.map_mul, AddValuation.map_mul, addVal_single_one, hδ, hδ,
    ← WithTop.coe_add, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem quadraticNew_middle_nonneg {F : Type*} [Field F] {M : Type*} [PseudoMetricSpace M]
    (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F
      (HahnSeries.single (dist r y - dist x y) (1 : F) * δ x) := by
  rw [AddValuation.map_mul, addVal_single_one, hδ, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr (by
    linarith [show dist x y ≤ dist r x + dist r y by
      simpa only [dist_comm x r] using dist_triangle x r y])

theorem addVal_pi_single_nonneg {F J : Type*} [Field F] [DecidableEq J]
    (j z : J) (a : HahnSeries ℝ F) (ha : (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F a) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F ((Pi.single j a : J → HahnSeries ℝ F) z) := by
  rw [Pi.single_apply]
  split_ifs
  · exact ha
  · simpa only [AddValuation.map_zero] using (le_top : (0 : WithTop ℝ) ≤ ⊤)

theorem quadraticNewCoefficients_nonneg {F : Type*} [Field F] {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (x y : M)
    (j : PUnit ⊕ (M ⊕ Sym2 M)) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticNewCoefficients r δ x y j) := by
  rcases j with u | (z | p)
  · exact quadraticNew_unit_nonneg r δ hδ x y
  · exact (le_min
      (addVal_pi_single_nonneg y z _ (quadraticNew_middle_nonneg r δ hδ x y))
      (addVal_pi_single_nonneg x z _ (by
        simpa only [dist_comm y x] using quadraticNew_middle_nonneg r δ hδ y x))).trans
      (AddValuation.map_add _ _ _)
  · exact addVal_pi_single_nonneg s(x, y) p 1 (by simp [AddValuation.map_one])

end KServerConj
end SharpFile017

-- Source: HahnMinorReindex.lean
section SharpFile018
namespace KServerConj

theorem det_row_equiv_tuple {R I I' J : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (G : Matrix I J R) (e : I' ≃ I) (x : I → J) :
    ((G.submatrix e id).submatrix id (x ∘ e)).det = (G.submatrix id x).det := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
    Matrix.det_submatrix_equiv_self e (G.submatrix id x)

theorem minorVal_row_equiv_le {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) ≤ minorVal G := by
  rw [minorVal_eq_embeddingMinorVal G]
  exact Finset.le_inf (fun x _ => (minorVal_le_tuple (G.submatrix e id) (x ∘ e)).trans_eq
    (congrArg (HahnSeries.addVal ℝ F) (det_row_equiv_tuple G e x)))

theorem minorVal_row_equiv {F I I' J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (e : I' ≃ I) :
    minorVal (G.submatrix e id) = minorVal G := by
  refine le_antisymm (minorVal_row_equiv_le G e) ?_
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Function.comp_id,
    Matrix.submatrix_id_id] using minorVal_row_equiv_le (G.submatrix e id) e.symm

end KServerConj
end SharpFile018

-- Source: MinorCombination.lean
section SharpFile019
open scoped BigOperators

namespace DetValuationMilestone

theorem det_mul_rectangular_expansion
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (G : Matrix I J R) (C : Matrix J I R) :
    (G * C).det =
      ∑ f : I → J, (∏ i, C (f i) i) * (G.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq,
    mul_comm, mul_assoc]

theorem valuation_prod_nonneg
    {R I : Type*} [CommMonoid R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (s : Finset I) (f : I → R)
    (hf : ∀ i ∈ s, (0 : WithTop ℝ) ≤ ν (f i)) :
    (0 : WithTop ℝ) ≤ ν (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hone]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, hmul]
    exact add_nonneg (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem valuation_det_mul_lower_bound
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J I R) (μ : WithTop ℝ)
    (hG : ∀ f : I → J, μ ≤ ν (G.submatrix id f).det)
    (hC : ∀ j i, (0 : WithTop ℝ) ≤ ν (C j i)) :
    μ ≤ ν (G * C).det := by
  rw [det_mul_rectangular_expansion]
  apply valuation_sum_lower_bound ν hzero hadd
  intro f _
  have hcoeff : (0 : WithTop ℝ) ≤ ν (∏ i, C (f i) i) :=
    valuation_prod_nonneg ν hone hmul Finset.univ (fun i => C (f i) i)
      (fun i _ => hC (f i) i)
  simpa only [hmul, zero_add] using add_le_add hcoeff (hG f)

theorem tupleMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    tupleMinorVal ν G ≤ tupleMinorVal ν (G * C) := by
  classical
  refine Finset.le_inf (fun e _ => ?_)
  change tupleMinorVal ν G ≤ ν (G * (C.submatrix id e)).det
  exact valuation_det_mul_lower_bound ν hzero hone hmul hadd G (C.submatrix id e)
    (tupleMinorVal ν G)
    (fun f => Finset.inf_le (f := fun x : I → J => ν (G.submatrix id x).det)
      (Finset.mem_univ f))
    (fun j i => hC j (e i))

theorem embeddingMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν (G * C) := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    tupleMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C hC

theorem embeddingMinorVal_mono_of_column_combinations
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (F : Matrix I K R)
    (hF : ∀ k, ∃ c : J → R,
      (∀ j, (0 : WithTop ℝ) ≤ ν (c j)) ∧ ∀ i, F i k = ∑ j, G i j * c j) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν F := by
  classical
  let C : Matrix J K R := Matrix.of fun j k => (hF k).choose j
  have hGC : G * C = F :=
    Matrix.ext (fun i k => by
      simpa only [Matrix.mul_apply, C, Matrix.of_apply] using ((hF k).choose_spec.2 i).symm)
  simpa only [hGC] using
    embeddingMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C
      (fun j k => (hF k).choose_spec.1 j)

end DetValuationMilestone
end SharpFile019

-- Source: HahnMinorCombination.lean
section SharpFile020
open scoped BigOperators

namespace KServerConj

theorem minorVal_mono_of_column_combinations {F I J K : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (G : Matrix I J (HahnSeries ℝ F)) (A : Matrix I K (HahnSeries ℝ F))
    (hA : ∀ k, ∃ c : J → HahnSeries ℝ F,
      (∀ j, (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (c j)) ∧
      ∀ i, A i k = ∑ j, G i j * c j) :
    minorVal G ≤ minorVal A := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mono_of_column_combinations
      (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) (AddValuation.map_one _)
      (fun a b => AddValuation.map_mul _ a b) (fun a b => AddValuation.map_add _ a b)
      G A hA

end KServerConj
end SharpFile020

-- Source: PotentialNewCombinations.lean
section SharpFile021
open scoped BigOperators

namespace KServerConj

theorem quadraticNewReference_le_updated_minorVal {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) :
    minorVal (quadraticNewReference q r) ≤
      minorVal (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))) := by
  classical
  exact (minorVal_mono_of_column_combinations (quadraticNewReference q r)
    ((quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))).submatrix
      (quadraticThreeBlockEquiv m).symm id) (by
        intro c
        induction c using Sym2.ind with
        | _ x y =>
          exact ⟨quadraticNewCoefficients r δ x y,
            quadraticNewCoefficients_nonneg r δ hδ x y,
            quadraticNewColumn_expansion q r δ x y⟩)).trans_eq
      (minorVal_row_equiv (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y))))
        (quadraticThreeBlockEquiv m).symm)

end KServerConj
end SharpFile021

-- Source: MinorNonnegative.lean
section SharpFile022
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_det_nonneg
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix I I R) (hA : ∀ i j, (0 : WithTop ℝ) ≤ ν (A i j)) :
    (0 : WithTop ℝ) ≤ ν A.det := by
  let S : Subring R :=
    { carrier := {x | (0 : WithTop ℝ) ≤ ν x}
      zero_mem' := (show (0 : WithTop ℝ) ≤ ν 0 from
        hzero.symm ▸ (le_top : (0 : WithTop ℝ) ≤ ⊤))
      one_mem' := (show (0 : WithTop ℝ) ≤ ν 1 from
        hone.symm ▸ (le_rfl : (0 : WithTop ℝ) ≤ 0))
      add_mem' := fun hx hy => (le_min hx hy).trans (hadd _ _)
      neg_mem' := fun {x} hx => (show (0 : WithTop ℝ) ≤ ν (-x) from (hneg x).symm ▸ hx)
      mul_mem' := fun {x y} hx hy => (show (0 : WithTop ℝ) ≤ ν (x * y) from
        (hmul x y).symm ▸ add_nonneg hx hy) }
  let B : Matrix I I S := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hmatrix : S.subtype.mapMatrix B = A := Matrix.ext (fun _ _ => rfl)
  have hmap : (↑(B.det) : R) = A.det :=
    (RingHom.map_det S.subtype B).trans (congrArg Matrix.det hmatrix)
  exact hmap ▸ (show (0 : WithTop ℝ) ≤ ν (↑(B.det) : R) from (B.det).property)

theorem zero_le_tupleMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ tupleMinorVal ν G := by
  classical
  exact Finset.le_inf (fun e _ => valuation_det_nonneg ν hzero hone hneg hmul hadd
    (G.submatrix id e) (fun i j => hG i (e j)))

theorem zero_le_embeddingMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd G hG

end DetValuationMilestone
end SharpFile022

-- Source: RowReplacement.lean
section SharpFile023
open scoped BigOperators

namespace KServerAlgebra

theorem det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

theorem det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, updateCol_column_family] using
    det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

theorem rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

theorem det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [rowReplace_column_matrix]
  exact det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

theorem mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

theorem det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra
end SharpFile023

-- Source: MinorBlocks.lean
section SharpFile024
open scoped BigOperators

namespace DetValuationMilestone

theorem exists_finite_inf_minimizer
    {X : Type*} [Fintype X] (f : X → WithTop ℝ) (μ : ℝ)
    (h : (Finset.univ.inf f) = (μ : WithTop ℝ)) :
    ∃ x, f x = (μ : WithTop ℝ) := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.inf_le_iff (show (μ : WithTop ℝ) < ⊤ by simp)).mp h.le
  exact ⟨i, le_antisymm hi (h.symm.trans_le (Finset.inf_le (Finset.mem_univ i)))⟩

theorem minimum_basis_coordinate_nonneg
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field K]
    (ν : K → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (G : Matrix I J K) (x : I → J) (μ : ℝ)
    (hmin : tupleMinorVal ν G = (μ : WithTop ℝ))
    (hx : ν (G.submatrix id x).det = (μ : WithTop ℝ)) :
    ∀ i j, (0 : WithTop ℝ) ≤ ν (((G.submatrix id x)⁻¹ * G) i j) := by
  let A : Matrix I I K := G.submatrix id x
  have hval : ν A.det = (μ : WithTop ℝ) := hx
  have hAne : A.det ≠ 0 := fun hz =>
    (show (μ : WithTop ℝ) ≠ ⊤ by simp)
      ((hval.symm.trans (congrArg ν hz)).trans hzero)
  intro i j
  have hcr := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A (G.col j)
    (isUnit_iff_ne_zero.mpr hAne)) i
  have hcoord : A.det * ((A⁻¹ * G) i j) = (A.updateCol i (G.col j)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.col_apply] using hcr
  have hmodified : (A.updateCol i (G.col j)).det =
      (G.submatrix id (Function.update x i j)).det := by
    exact congrArg Matrix.det (Matrix.ext (fun a b => by
      by_cases hb : b = i <;>
        simp [A, Matrix.updateCol, Matrix.submatrix, Function.update, hb]))
  have hfull : (μ : WithTop ℝ) ≤ ν (G.submatrix id (Function.update x i j)).det :=
    hmin.symm.trans_le (Finset.inf_le (f := fun y : I → J => ν (G.submatrix id y).det)
      (Finset.mem_univ (Function.update x i j)))
  rw [← hmodified, ← hcoord, hmul, hval] at hfull
  exact WithTop.le_of_add_le_add_left (x := (μ : WithTop ℝ)) (by simp)
    (by simpa only [add_zero] using hfull)

theorem valuation_det_inverse_of_finite
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (A : Matrix I I R) (hA : IsUnit A.det) (μ : ℝ)
    (hval : ν A.det = (μ : WithTop ℝ)) :
    ν A⁻¹.det = ((-μ : ℝ) : WithTop ℝ) := by
  have hprod : ν A⁻¹.det + (μ : WithTop ℝ) = 0 := by
    simpa only [hmul, hval, hone] using congrArg ν (Matrix.det_nonsing_inv_mul_det A hA)
  exact (add_left_inj_of_ne_top (a := (μ : WithTop ℝ)) (by simp)).mp
    (by simpa only [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero] using hprod)

theorem submatrix_fromBlocks_sum_map
    {I₁ I₂ J₁ J₂ R : Type*} [Zero R]
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R)
    (x₁ : I₁ → J₁) (x₂ : I₂ → J₂) :
    (Matrix.fromBlocks G₁ 0 0 G₂).submatrix id (Sum.map x₁ x₂) =
      Matrix.fromBlocks (G₁.submatrix id x₁) 0 0 (G₂.submatrix id x₂) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem tupleMinorVal_fromBlocks_of_finite
    {I₁ I₂ J₁ J₂ R : Type*}
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂] [Field R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ a, ν (-a) = ν a)
    (hmul : ∀ a b, ν (a * b) = ν a + ν b)
    (hadd : ∀ a b, min (ν a) (ν b) ≤ ν (a + b))
    (G₁ : Matrix I₁ J₁ R) (G₂ : Matrix I₂ J₂ R) (μ₁ μ₂ : ℝ)
    (hmin₁ : tupleMinorVal ν G₁ = (μ₁ : WithTop ℝ))
    (hmin₂ : tupleMinorVal ν G₂ = (μ₂ : WithTop ℝ)) :
    tupleMinorVal ν (Matrix.fromBlocks G₁ 0 0 G₂) = ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
  obtain ⟨x₁, hx₁⟩ := exists_finite_inf_minimizer
    (fun x : I₁ → J₁ => ν (G₁.submatrix id x).det) μ₁ hmin₁
  obtain ⟨x₂, hx₂⟩ := exists_finite_inf_minimizer
    (fun x : I₂ → J₂ => ν (G₂.submatrix id x).det) μ₂ hmin₂
  let A₁ : Matrix I₁ I₁ R := G₁.submatrix id x₁
  let A₂ : Matrix I₂ I₂ R := G₂.submatrix id x₂
  let S : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R := Matrix.fromBlocks G₁ 0 0 G₂
  let B : Matrix (I₁ ⊕ I₂) (I₁ ⊕ I₂) R := Matrix.fromBlocks A₁⁻¹ 0 0 A₂⁻¹
  let H : Matrix (I₁ ⊕ I₂) (J₁ ⊕ J₂) R :=
    Matrix.fromBlocks (A₁⁻¹ * G₁) 0 0 (A₂⁻¹ * G₂)
  have hproduct : B * S = H := by
    simp only [B, S, H, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero]
  have hn₁ := minimum_basis_coordinate_nonneg ν hzero hmul G₁ x₁ μ₁ hmin₁ hx₁
  have hn₂ := minimum_basis_coordinate_nonneg ν hzero hmul G₂ x₂ μ₂ hmin₂ hx₂
  have hH : ∀ (i : I₁ ⊕ I₂) (j : J₁ ⊕ J₂), (0 : WithTop ℝ) ≤ ν (H i j) := fun
    | Sum.inl i, Sum.inl j => hn₁ i j
    | Sum.inl i, Sum.inr j => by simp [H, hzero]
    | Sum.inr i, Sum.inl j => by simp [H, hzero]
    | Sum.inr i, Sum.inr j => hn₂ i j
  have hHmin := zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd H hH
  have hrow : tupleMinorVal ν H = ν B.det + tupleMinorVal ν S :=
    (congrArg (tupleMinorVal ν) hproduct).symm.trans (tupleMinorVal_mul ν hmul B S)
  have hunit₁ : IsUnit A₁.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₁ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₁.symm.trans (congrArg ν hz)).trans hzero))
  have hunit₂ : IsUnit A₂.det := isUnit_iff_ne_zero.mpr (fun hz =>
    (show (μ₂ : WithTop ℝ) ≠ ⊤ by simp)
      ((hx₂.symm.trans (congrArg ν hz)).trans hzero))
  have hinv₁ := valuation_det_inverse_of_finite ν hone hmul A₁ hunit₁ μ₁ hx₁
  have hinv₂ := valuation_det_inverse_of_finite ν hone hmul A₂ hunit₂ μ₂ hx₂
  have hBval : ν B.det = ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) := by
    simp only [B, Matrix.det_fromBlocks_zero₂₁, hmul, hinv₁, hinv₂, ← WithTop.coe_add]
  have hscaled : (0 : WithTop ℝ) ≤ ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ) + tupleMinorVal ν S := by
    simpa only [hrow, hBval] using hHmin
  have hlower : ((μ₁ + μ₂ : ℝ) : WithTop ℝ) ≤ tupleMinorVal ν S :=
    WithTop.le_of_add_le_add_left (x := ((-μ₁ + -μ₂ : ℝ) : WithTop ℝ)) (by simp)
      (by simpa only [← WithTop.coe_add,
        show (-μ₁ + -μ₂) + (μ₁ + μ₂) = 0 by linarith only,
        WithTop.coe_zero] using hscaled)
  have hselected : tupleMinorVal ν S ≤ ν (S.submatrix id (Sum.map x₁ x₂)).det :=
    Finset.inf_le (f := fun x : (I₁ ⊕ I₂) → (J₁ ⊕ J₂) => ν (S.submatrix id x).det)
      (Finset.mem_univ (Sum.map x₁ x₂))
  have hupper : tupleMinorVal ν S ≤ ((μ₁ + μ₂ : ℝ) : WithTop ℝ) := by
    simpa only [S, submatrix_fromBlocks_sum_map, Matrix.det_fromBlocks_zero₂₁,
      hmul, hx₁, hx₂, ← WithTop.coe_add] using hselected
  exact le_antisymm hupper hlower

end DetValuationMilestone
end SharpFile024

-- Source: HahnMinorBlocks.lean
section SharpFile025
namespace KServerConj

theorem tupleMinorVal_one_punit {F : Type*} [Field F] :
    DetValuationMilestone.tupleMinorVal (HahnSeries.addVal ℝ F)
      (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  classical
  simp [DetValuationMilestone.tupleMinorVal, Matrix.det_unique, Matrix.submatrix_apply,
    AddValuation.map_one]

theorem minorVal_one_punit {F : Type*} [Field F] :
    minorVal (1 : Matrix PUnit PUnit (HahnSeries ℝ F)) = (0 : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      (tupleMinorVal_one_punit (F := F))

set_option maxHeartbeats 1000000 in
theorem minorVal_fromBlocks_of_finite {F I₁ I₂ J₁ J₂ : Type*} [Field F]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype J₁] [Fintype J₂]
    (G₁ : Matrix I₁ J₁ (HahnSeries ℝ F)) (G₂ : Matrix I₂ J₂ (HahnSeries ℝ F))
    (a b : ℝ) (h₁ : minorVal G₁ = (a : WithTop ℝ)) (h₂ : minorVal G₂ = (b : WithTop ℝ)) :
    minorVal (Matrix.fromBlocks G₁ 0 0 G₂) = ((a + b : ℝ) : WithTop ℝ) := by
  simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using
      DetValuationMilestone.tupleMinorVal_fromBlocks_of_finite (R := HahnSeries ℝ F)
        (HahnSeries.addVal ℝ F) (AddValuation.map_zero (HahnSeries.addVal ℝ F))
        (AddValuation.map_one (HahnSeries.addVal ℝ F))
        (fun x => AddValuation.map_neg (HahnSeries.addVal ℝ F) x)
        (fun x y => AddValuation.map_mul (HahnSeries.addVal ℝ F) x y)
        (fun x y => AddValuation.map_add (HahnSeries.addVal ℝ F) x y) G₁ G₂ a b
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₁)
        (by
          simpa only [DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
            (HahnSeries.addVal ℝ F) (AddValuation.map_zero _), ← minorVal_eq_embeddingMinorVal] using h₂)

end KServerConj
end SharpFile025

-- Source: field/InitialColumns.lean
section SharpFile026
namespace KServerConj

noncomputable def initCols {k : ℕ} {M : Type*} [PseudoMetricSpace M] (s : Fin k → M) :
    M → Fin k → K k M :=
  fun x i => coef (Sum.inl (i, x)) * zp (dist (s i) x)

noncomputable def colDet {k : ℕ} {M : Type*} (q : M → Fin k → K k M) (X : Fin k → M) : K k M :=
  (Matrix.of fun i j => q (X j) i).det

end KServerConj
end SharpFile026

-- Source: field/RequestColumns.lean
section SharpFile027
namespace KServerConj

noncomputable def rowReplace {m : ℕ} {M : Type*} (q : M → Fin (m + 1) → K (m + 1) M)
    (δ : M → K (m + 1) M) : M → Fin (m + 1) → K (m + 1) M :=
  fun x => Fin.cons (δ x) (Fin.tail (q x))

noncomputable def freshRow {m : ℕ} {M : Type*} [PseudoMetricSpace M] (r : ℕ → M) (t : ℕ) :
    M → K (m + 1) M :=
  fun x => coef (Sum.inr (t, x)) * zp (dist (r t) x)

end KServerConj
end SharpFile027

-- Source: field/ValuationLaws.lean
section SharpFile028
namespace KServerConj

variable {k : ℕ} {M : Type*}

@[simp] theorem nu_zero : nu (0 : K k M) = ⊤ := by
  exact AddValuation.map_zero _

@[simp] theorem nu_one : nu (1 : K k M) = 0 := by
  exact AddValuation.map_one _

@[simp] theorem nu_eq_top_iff (f : K k M) : nu f = ⊤ ↔ f = 0 := by
  exact HahnSeries.orderTop_eq_top

theorem nu_mul (f g : K k M) : nu (f * g) = nu f + nu g := by
  exact AddValuation.map_mul _ f g

theorem nu_add (f g : K k M) : min (nu f) (nu g) ≤ nu (f + g) := by
  exact AddValuation.map_add _ f g

@[simp] theorem nu_zp (a : ℝ) : nu (zp a : K k M) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem varF_ne_zero (v : Var k M) : varF v ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))).mpr
    (MvPolynomial.X_ne_zero v)

@[simp] theorem nu_coef (v : Var k M) : nu (coef v) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, coef, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) (varF_ne_zero v))

theorem nu_C {c : F k M} (hc : c ≠ 0) : nu (HahnSeries.C c : K k M) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) hc)

theorem coef_ne_zero (v : Var k M) : coef v ≠ 0 := by
  exact HahnSeries.single_ne_zero (varF_ne_zero v)

theorem zp_ne_zero (a : ℝ) : (zp a : K k M) ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem zp_zero : (zp 0 : K k M) = 1 := by
  exact HahnSeries.single_zero_one

theorem zp_add (a b : ℝ) : (zp (a + b) : K k M) = zp a * zp b := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F k M)) (s := 1)).symm

@[simp] theorem nu_neg (f : K k M) : nu (-f) = nu f := by
  exact AddValuation.map_neg _ _

@[simp] theorem nu_inv (f : K k M) : nu f⁻¹ = -(nu f) := by
  exact AddValuation.map_inv _

theorem nu_sum_ge {ι : Type*} [Fintype ι] (f : ι → K k M) (b : WithTop ℝ)
    (hf : ∀ i, b ≤ nu (f i)) : b ≤ nu (∑ i, f i) := by
  exact AddValuation.map_le_sum _ (fun i _ => hf i)

theorem nu_fresh_term (v : Var k M) (a : ℝ) (f : K k M) :
    nu (coef v * zp a * f) = (a : WithTop ℝ) + nu f := by
  simp only [nu_mul, nu_coef, nu_zp, zero_add]

theorem zp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (zp (∑ i ∈ s, a i) : K k M) = ∏ i ∈ s, zp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, zp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zp_add, ih]

end KServerConj
end SharpFile028

-- Source: PotentialNewBound.lean
section SharpFile029
namespace KServerConj

theorem quadraticNewReference_minorVal {F : Type*} [Field F] {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (b c : ℝ)
    (hH : minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ))
    (hQ : minorVal (quadraticMatrix (fun y => Fin.tail (q y))) = (c : WithTop ℝ)) :
    minorVal (quadraticNewReference q r) = ((b + c : ℝ) : WithTop ℝ) := by
  simpa only [quadraticNewReference, zero_add] using
    minorVal_fromBlocks_of_finite (1 : Matrix PUnit PUnit (HahnSeries ℝ F))
      (Matrix.fromBlocks ((weightedColumns q r).submatrix Fin.succ id) 0 0
        (quadraticMatrix (fun y => Fin.tail (q y)))) 0 (b + c) minorVal_one_punit
      (minorVal_fromBlocks_of_finite _ _ b c hH hQ)

theorem quadratic_new_potential_lower_bound {F : Type*} [Field F]
    {m : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (m + 1) → HahnSeries ℝ F) (r : M) (δ : M → HahnSeries ℝ F)
    (hδ : ∀ x, HahnSeries.addVal ℝ F (δ x) = (dist r x : WithTop ℝ)) (b c : ℝ)
    (hH : minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ))
    (hQ : minorVal (quadraticMatrix (fun y => Fin.tail (q y))) = (c : WithTop ℝ)) :
    ((b + c : ℝ) : WithTop ℝ) ≤
      minorVal (quadraticMatrix (fun y => Fin.cons (δ y) (Fin.tail (q y)))) := by
  exact (quadraticNewReference_minorVal.{_, _, 0} q r b c hH hQ).symm.trans_le
    (quadraticNewReference_le_updated_minorVal q r δ hδ)

theorem fresh_new_potential_lower_bound {m : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin (m + 1) → K (m + 1) M) (r : M) (t : ℕ) (b c : ℝ)
    (hH : minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ))
    (hQ : minorVal (quadraticMatrix (fun y => Fin.tail (q y))) = (c : WithTop ℝ)) :
    ((b + c : ℝ) : WithTop ℝ) ≤
      Psi (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) := by
  exact quadratic_new_potential_lower_bound q r
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y))
    (fun y => by simp only [nu_mul, nu_coef, nu_zp, zero_add]) b c hH hQ

end KServerConj
end SharpFile029

-- Source: SymmetricSquareDet.lean
section SharpFile030
open scoped BigOperators

namespace KServerConj

theorem det_eq_one_of_weight {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (weight : ι → ℕ)
    (h : ∀ i j, weight j ≤ weight i → A i j = (1 : Matrix ι ι R) i j) :
    A.det = 1 := by
  have ht : A.BlockTriangular weight := by
    intro i j hij
    rw [h i j hij.le]
    exact Matrix.one_apply_ne (fun he => (ne_of_lt hij) (congrArg weight he).symm)
  have hb (n : ℕ) : A.toSquareBlock weight n = 1 := by
    ext i j
    change A i.val j.val = (1 : Matrix { a // weight a = n } { a // weight a = n } R) i j
    simpa [Matrix.one_apply, Subtype.ext_iff] using
      h i.val j.val (le_of_eq (j.property.trans i.property.symm))
  simpa [hb] using ht.det

def symCount {ι : Type*} [DecidableEq ι] (a : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => (if i = a then 1 else 0) + (if j = a then 1 else 0), by
    intro i j
    exact Nat.add_comm _ _⟩

@[simp] theorem symCount_mk {ι : Type*} [DecidableEq ι] (a i j : ι) :
    symCount a s(i, j) = (if i = a then 1 else 0) + (if j = a then 1 else 0) := rfl

theorem transvection_col {R : Type*} [CommRing R] {k : ℕ}
    (i j l : Fin k) (c : R) :
    (Matrix.transvection i j c).col l =
      Pi.single l 1 + if l = j then c • Pi.single i 1 else 0 := by
  ext r
  by_cases hl : l = j <;> by_cases hr : r = i <;>
    simp_all [Matrix.transvection, Matrix.col, Matrix.single, Matrix.one_apply,
      Pi.single_apply, eq_comm]

theorem sym2Mat_transvection_weight {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) (p q : Sym2 (Fin k))
    (hw : symCount j q ≤ symCount j p) :
    sym2Mat (Matrix.transvection i j c) p q = (1 : Matrix _ _ R) p q := by
  have hz (z : Sym2 (Fin k)) (hzp : symCount j z < symCount j p) :
      (Pi.single z (1 : R) : Sym2 (Fin k) → R) p = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Sym2 (Fin k) => R)
      (fun he => hzp.ne (congrArg (symCount j) he).symm) (1 : R)
  induction q using Sym2.ind with
  | _ x y =>
    change symProd ((Matrix.transvection i j c).col x)
      ((Matrix.transvection i j c).col y) p = _
    by_cases hx : x = j <;> by_cases hy : y = j
    · have h0 := hz s(i, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      have h1 := hz s(i, j) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, symProd_add_left,
        symProd_add_right, symProd_smul_left, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        show s(j, i) = s(i, j) from Sym2.eq_swap, h0, h1, mul_zero, add_zero]
      simp [hx, hy, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(i, y) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_left, symProd_smul_left, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hx, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(x, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_right, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hy, Matrix.one_apply, Pi.single_apply]
    · simp [transvection_col, hx, hy, symProd_single_single, Matrix.one_apply, Pi.single_apply]

theorem det_sym2Mat_transvection {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) :
    (sym2Mat (Matrix.transvection i j c)).det = 1 := by
  exact det_eq_one_of_weight _ (symCount j) (sym2Mat_transvection_weight i j c hij)

theorem sym2_mk_left_injective {ι : Type*} (i : ι) :
    Function.Injective (fun j : ι => s(i, j)) :=
  fun _ _ h => (Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1)

theorem symCount_eq_zero_of_not_mem_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : Sym2 ι)
    (hp : p ∉ Finset.univ.image (fun j : ι => s(i, j))) : symCount i p = 0 := by
  induction p using Sym2.ind with
  | _ x y =>
    have hx : x ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, congrArg (fun a => s(a, y)) h.symm⟩)
    have hy : y ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, (Sym2.eq_swap : s(i, x) = s(x, i)).trans
        (congrArg (fun a => s(x, a)) h.symm)⟩)
    simp [symCount_mk, hx, hy]

theorem sum_symCount {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ p : Sym2 ι, symCount i p = Fintype.card ι + 1 := by
  have hs : (∑ p ∈ Finset.univ.image (fun j : ι => s(i, j)), symCount i p) =
      ∑ p : Sym2 ι, symCount i p :=
    Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => symCount_eq_zero_of_not_mem_image i p hp)
  rw [← hs, Finset.sum_image (sym2_mk_left_injective i).injOn]
  simp [symCount_mk, Finset.sum_add_distrib]

def symPairMul {ι R : Type*} [CommMonoid R] (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

@[simp] theorem symPairMul_mk {ι R : Type*} [CommMonoid R]
    (d : ι → R) (i j : ι) : symPairMul d s(i, j) = d i * d j := rfl

theorem symPairMul_eq_prod {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) (p : Sym2 ι) :
    symPairMul d p = ∏ i : ι, d i ^ symCount i p := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [symPairMul_mk, symCount_mk, pow_add, Finset.prod_mul_distrib]
    simp only [Finset.prod_pow_boole, Finset.mem_univ, ite_true]

theorem prod_symPairMul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) :
    (∏ p : Sym2 ι, symPairMul d p) = (∏ i : ι, d i) ^ (Fintype.card ι + 1) := by
  simp_rw [symPairMul_eq_prod]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_symCount]
  exact Finset.prod_pow _ _ _

theorem sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    sym2Mat (Matrix.diagonal d) = Matrix.diagonal (symPairMul d) := by
  have hs (i : Fin k) (a : R) :
      (Pi.single i a : Fin k → R) = a • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i a (1 : R)
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [Matrix.mulVec_single_one, sym2Mat_col, Matrix.col_diagonal, symPairMul_mk]
    rw [hs i (d i), hs j (d j), symProd_smul_left, symProd_smul_right,
      symProd_single_single, smul_smul]
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]

theorem det_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    (sym2Mat (Matrix.diagonal d)).det = (Matrix.diagonal d).det ^ (k + 1) := by
  simp only [sym2Mat_diagonal, Matrix.det_diagonal, prod_symPairMul, Fintype.card_fin]

theorem det_sym2Mat {K : Type*} [Field K] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply Matrix.diagonal_transvection_induction
    (fun M : Matrix (Fin k) (Fin k) K => (sym2Mat M).det = M.det ^ (k + 1)) A
  · exact fun d _ => det_sym2Mat_diagonal d
  · intro t
    simpa [Matrix.TransvectionStruct.toMatrix, t.hij] using
      det_sym2Mat_transvection t.i t.j t.c t.hij
  · intro M N hM hN
    rw [sym2Mat_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

end KServerConj
end SharpFile030

-- Source: Theorems/Thm_KServer_workFn_rec_le.lean
section SharpFile034
open KServer

private theorem sharpFile034_moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sharpFile034_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem sharpFile034_moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sharpFile034_sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def sharpFile034_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile034_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile034_Wset C₀ σ X) := rfl

private theorem sharpFile034_Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (sharpFile034_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile034_sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile034_Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (sharpFile034_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile034_moveCost_nonneg _ _
  have h2 := sharpFile034_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile034_wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [sharpFile034_workFn_eq]
  refine le_csInf (sharpFile034_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile034_moveCost_nonneg _ _
  have h2 := sharpFile034_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile034_wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [sharpFile034_workFn_eq, sharpFile034_workFn_eq]
  have hkey : ∀ c ∈ sharpFile034_Wset C₀ σ Y, sInf (sharpFile034_Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ sharpFile034_Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (sharpFile034_Wset_bdd C₀ σ X) hmem
    have h2 := sharpFile034_moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (sharpFile034_Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

private theorem sharpFile034_wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [sharpFile034_workFn_eq, sharpFile034_workFn_eq]
  refine le_csInf (sharpFile034_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ sharpFile034_Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (sharpFile034_Wset_bdd C₀ σ X) hmem
  have h2 := sharpFile034_moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sharpFile034_sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

private theorem sharpFile034_wf_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (sharpFile034_wf_mono k hk M C₀ σ r X)
  rw [sharpFile034_workFn_eq, sharpFile034_workFn_eq]
  refine csInf_le_csInf (sharpFile034_Wset_bdd C₀ (σ ++ [r]) X) (sharpFile034_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, sharpFile034_moveCost_self]
  ring

private theorem sharpFile034_moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sharpFile034_sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

theorem KServer.workFn_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFn C₀ (σ ++ [r]) X ≤ workFn C₀ σ (Function.update X i r) + dist r (X i) := by
  classical
  rw [sharpFile034_workFn_eq, sharpFile034_workFn_eq]
  set X' : Config k M := Function.update X i r with hX'def
  have hkey : ∀ c ∈ sharpFile034_Wset C₀ σ X', sInf (sharpFile034_Wset C₀ (σ ++ [r]) X) - dist r (X i) ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    set n := σ.length with hn
    have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
    set S' : ℕ → Config k M := fun j => if j = n + 1 then X' else S j with hS'def
    have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
      intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
    have hS'top : S' (n + 1) = X' := by rw [hS'def]; simp
    have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
      refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
      intro j
      have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
      by_cases hjn : (j : ℕ) = n
      · refine ⟨i, ?_⟩
        rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hX'def, Function.update_self]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        simp [hjn, hn]
      · obtain ⟨i2, hi2⟩ := hS.2 ⟨(j : ℕ), by omega⟩
        refine ⟨i2, ?_⟩
        rw [hS'ne _ (by omega), hi2]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left (by omega)]
    have hmem : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X ∈ sharpFile034_Wset C₀ (σ ++ [r]) X := ⟨S', hserves, rfl⟩
    have hval : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X
        = ((∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) X')
          + dist r (X i) := by
      rw [hlen, Finset.sum_range_succ]
      have e1 : ∀ j ∈ Finset.range n,
          moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hS'ne _ (by omega), hS'ne _ (by omega)]
      rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, hX'def, sharpFile034_moveCost_update]
    rw [hval] at hmem
    have h1 := csInf_le (sharpFile034_Wset_bdd C₀ (σ ++ [r]) X) hmem
    linarith
  have := le_csInf (sharpFile034_Wset_nonempty k hk M C₀ σ X') hkey
  linarith
end SharpFile034

-- Source: Theorems/Thm_KServer_workFn_rec_ge.lean
section SharpFile035
open KServer

private theorem sharpFile035_moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sharpFile035_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem sharpFile035_moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sharpFile035_sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def sharpFile035_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile035_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile035_Wset C₀ σ X) := rfl

private theorem sharpFile035_Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (sharpFile035_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile035_sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile035_Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (sharpFile035_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile035_moveCost_nonneg _ _
  have h2 := sharpFile035_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile035_wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [sharpFile035_workFn_eq]
  refine le_csInf (sharpFile035_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile035_moveCost_nonneg _ _
  have h2 := sharpFile035_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile035_wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [sharpFile035_workFn_eq, sharpFile035_workFn_eq]
  have hkey : ∀ c ∈ sharpFile035_Wset C₀ σ Y, sInf (sharpFile035_Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ sharpFile035_Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (sharpFile035_Wset_bdd C₀ σ X) hmem
    have h2 := sharpFile035_moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (sharpFile035_Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

private theorem sharpFile035_wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [sharpFile035_workFn_eq, sharpFile035_workFn_eq]
  refine le_csInf (sharpFile035_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ sharpFile035_Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (sharpFile035_Wset_bdd C₀ σ X) hmem
  have h2 := sharpFile035_moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sharpFile035_sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

private theorem sharpFile035_wf_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (sharpFile035_wf_mono k hk M C₀ σ r X)
  rw [sharpFile035_workFn_eq, sharpFile035_workFn_eq]
  refine csInf_le_csInf (sharpFile035_Wset_bdd C₀ (σ ++ [r]) X) (sharpFile035_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, sharpFile035_moveCost_self]
  ring

private theorem sharpFile035_moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sharpFile035_sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

private theorem sharpFile035_wf_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFn C₀ (σ ++ [r]) X ≤ workFn C₀ σ (Function.update X i r) + dist r (X i) := by
  classical
  rw [sharpFile035_workFn_eq, sharpFile035_workFn_eq]
  set X' : Config k M := Function.update X i r with hX'def
  have hkey : ∀ c ∈ sharpFile035_Wset C₀ σ X', sInf (sharpFile035_Wset C₀ (σ ++ [r]) X) - dist r (X i) ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    set n := σ.length with hn
    have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
    set S' : ℕ → Config k M := fun j => if j = n + 1 then X' else S j with hS'def
    have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
      intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
    have hS'top : S' (n + 1) = X' := by rw [hS'def]; simp
    have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
      refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
      intro j
      have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
      by_cases hjn : (j : ℕ) = n
      · refine ⟨i, ?_⟩
        rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hX'def, Function.update_self]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        simp [hjn, hn]
      · obtain ⟨i2, hi2⟩ := hS.2 ⟨(j : ℕ), by omega⟩
        refine ⟨i2, ?_⟩
        rw [hS'ne _ (by omega), hi2]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left (by omega)]
    have hmem : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X ∈ sharpFile035_Wset C₀ (σ ++ [r]) X := ⟨S', hserves, rfl⟩
    have hval : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X
        = ((∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) X')
          + dist r (X i) := by
      rw [hlen, Finset.sum_range_succ]
      have e1 : ∀ j ∈ Finset.range n,
          moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hS'ne _ (by omega), hS'ne _ (by omega)]
      rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, hX'def, sharpFile035_moveCost_update]
    rw [hval] at hmem
    have h1 := csInf_le (sharpFile035_Wset_bdd C₀ (σ ++ [r]) X) hmem
    linarith
  have := le_csInf (sharpFile035_Wset_nonempty k hk M C₀ σ X') hkey
  linarith

theorem KServer.workFn_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFn C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFn C₀ (σ ++ [r]) X := by
  classical
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
    refine ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' hne
    (fun i => workFn C₀ σ (Function.update X i r) + dist r (X i))
  refine ⟨i₀, ?_⟩
  rw [← hi₀, sharpFile035_workFn_eq]
  refine le_csInf (sharpFile035_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  
  have hreq : (σ ++ [r]).get ⟨n, by rw [hlen]; omega⟩ = r := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (by omega)]
    simp [hn]
  obtain ⟨i₁, hi₁⟩ := hS.2 ⟨n, by rw [hlen]; omega⟩
  rw [hreq] at hi₁
  set Y : Config k M := Function.update X i₁ r with hYdef
  
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by rw [hlen]; omega⟩
    refine ⟨i, ?_⟩
    rw [hi]
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_left (by omega)]
  have hmemY : (∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) Y
      ∈ sharpFile035_Wset C₀ σ Y := ⟨S, hserve, rfl⟩
  have hwY : workFn C₀ σ Y
      ≤ (∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) Y := by
    rw [sharpFile035_workFn_eq]; exact csInf_le (sharpFile035_Wset_bdd C₀ σ Y) hmemY
  
  have hmv : moveCost (S (n + 1)) Y = moveCost (S (n + 1)) X - dist r (X i₁) := by
    have h : (∑ j, dist (S (n + 1) j) (Y j)) - (∑ j, dist (S (n + 1) j) (X j))
        = dist (S (n + 1) i₁) (Y i₁) - dist (S (n + 1) i₁) (X i₁) :=
      sharpFile035_sum_diff_single (fun j => dist (S (n + 1) j) (Y j))
        (fun j => dist (S (n + 1) j) (X j)) i₁
        (fun j hj => by
          show dist (S (n + 1) j) (Y j) = dist (S (n + 1) j) (X j)
          rw [hYdef, Function.update_of_ne hj])
    rw [hYdef, Function.update_self, hi₁, dist_self] at h
    unfold moveCost
    linarith
  have htri := sharpFile035_moveCost_triangle (S n) (S (n + 1)) Y
  have hfi : workFn C₀ σ (Function.update X i₁ r) + dist r (X i₁)
      ≤ (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S j) (S (j + 1)))
        + moveCost (S (σ ++ [r]).length) X := by
    rw [hlen, Finset.sum_range_succ, ← hYdef]
    linarith
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ i₁)) hfi
end SharpFile035

-- Source: Theorems/Thm_KServer_workFn_covered.lean
section SharpFile036
open KServer

private theorem sharpFile036_moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sharpFile036_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem sharpFile036_moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sharpFile036_sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def sharpFile036_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile036_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile036_Wset C₀ σ X) := rfl

private theorem sharpFile036_Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (sharpFile036_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile036_sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile036_Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (sharpFile036_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile036_moveCost_nonneg _ _
  have h2 := sharpFile036_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile036_wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [sharpFile036_workFn_eq]
  refine le_csInf (sharpFile036_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile036_moveCost_nonneg _ _
  have h2 := sharpFile036_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile036_wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [sharpFile036_workFn_eq, sharpFile036_workFn_eq]
  have hkey : ∀ c ∈ sharpFile036_Wset C₀ σ Y, sInf (sharpFile036_Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ sharpFile036_Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (sharpFile036_Wset_bdd C₀ σ X) hmem
    have h2 := sharpFile036_moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (sharpFile036_Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

private theorem sharpFile036_wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [sharpFile036_workFn_eq, sharpFile036_workFn_eq]
  refine le_csInf (sharpFile036_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ sharpFile036_Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (sharpFile036_Wset_bdd C₀ σ X) hmem
  have h2 := sharpFile036_moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sharpFile036_sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

theorem KServer.workFn_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (sharpFile036_wf_mono k hk M C₀ σ r X)
  rw [sharpFile036_workFn_eq, sharpFile036_workFn_eq]
  refine csInf_le_csInf (sharpFile036_Wset_bdd C₀ (σ ++ [r]) X) (sharpFile036_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, sharpFile036_moveCost_self]
  ring

private theorem sharpFile036_moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sharpFile036_sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h
end SharpFile036

-- Source: Theorems/Thm_KServer_workFnU_resolves.lean
section SharpFile037
open KServer

private theorem sharpFile037_wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem sharpFile037_wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem sharpFile037_update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

theorem KServer.wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := sharpFile037_wfU_exists C₀ σ (Function.update X i r)
  have h1 := sharpFile037_wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← sharpFile037_update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

theorem KServer.wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := sharpFile037_wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [sharpFile037_update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := sharpFile037_wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

theorem KServer.wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem sharpFile037_wfU_step_self (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) U
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) + dist r (U i) := by
  classical
  obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ σ r U
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    have := wfU_rec_le k hk M C₀ σ r U i
    rw [← hc] at this
    exact this
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    rw [hc]
    exact hi

theorem KServer.workFnU_resolves (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) X
      = workFnU C₀ (σ ++ [r]) (Function.update X i r) + dist r (X i) :=
  sharpFile037_wfU_step_self k hk M C₀ σ r X
end SharpFile037

-- Source: Theorems/Thm_KServer_workFn_mono.lean
section SharpFile038
open KServer

private theorem sharpFile038_moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sharpFile038_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem sharpFile038_moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sharpFile038_sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def sharpFile038_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile038_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile038_Wset C₀ σ X) := rfl

private theorem sharpFile038_Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (sharpFile038_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile038_sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile038_Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (sharpFile038_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile038_moveCost_nonneg _ _
  have h2 := sharpFile038_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile038_wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [sharpFile038_workFn_eq]
  refine le_csInf (sharpFile038_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile038_moveCost_nonneg _ _
  have h2 := sharpFile038_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile038_wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [sharpFile038_workFn_eq, sharpFile038_workFn_eq]
  have hkey : ∀ c ∈ sharpFile038_Wset C₀ σ Y, sInf (sharpFile038_Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ sharpFile038_Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (sharpFile038_Wset_bdd C₀ σ X) hmem
    have h2 := sharpFile038_moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (sharpFile038_Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

theorem KServer.workFn_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [sharpFile038_workFn_eq, sharpFile038_workFn_eq]
  refine le_csInf (sharpFile038_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ sharpFile038_Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (sharpFile038_Wset_bdd C₀ σ X) hmem
  have h2 := sharpFile038_moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sharpFile038_sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring
end SharpFile038

-- Source: Theorems/Thm_KServer_workFnU_mono.lean
section SharpFile039
open KServer

private theorem sharpFile039_wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem sharpFile039_wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem sharpFile039_mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

theorem KServer.workFnU_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := sharpFile039_wfU_exists C₀ (σ ++ [r]) X
  rw [← hπ]
  exact le_trans (sharpFile039_wfU_le C₀ σ X π) (workFn_mono k hk M C₀ σ r (X ∘ π))
end SharpFile039

-- Source: Theorems/Thm_KServer_workFnU_perm.lean
section SharpFile040
open KServer

private theorem sharpFile040_wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem sharpFile040_wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem sharpFile040_mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

theorem KServer.workFnU_perm (k : ℕ) (M : Type) [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (τ : Equiv.Perm (Fin k)) :
    workFnU C₀ σ (X ∘ τ) = workFnU C₀ σ X := by
  refine le_antisymm ?_ ?_
  · obtain ⟨π, hπ⟩ := sharpFile040_wfU_exists C₀ σ X
    have hcomp : (X ∘ (τ : Equiv.Perm (Fin k))) ∘ ((τ⁻¹ * π : Equiv.Perm (Fin k)) :
        Fin k → Fin k) = X ∘ (π : Equiv.Perm (Fin k)) := by
      funext i; simp
    have h := sharpFile040_wfU_le C₀ σ (X ∘ (τ : Equiv.Perm (Fin k))) (τ⁻¹ * π)
    rw [hcomp, hπ] at h
    exact h
  · obtain ⟨π, hπ⟩ := sharpFile040_wfU_exists C₀ σ (X ∘ (τ : Equiv.Perm (Fin k)))
    have hcomp : X ∘ ((τ * π : Equiv.Perm (Fin k)) : Fin k → Fin k)
        = (X ∘ (τ : Equiv.Perm (Fin k))) ∘ (π : Equiv.Perm (Fin k)) := by
      funext i; simp
    have h := sharpFile040_wfU_le C₀ σ X (τ * π)
    rw [hcomp, hπ] at h
    exact h
end SharpFile040

-- Source: Theorems/Thm_KServer_workFn_nil.lean
section SharpFile041
open KServer

private def sharpFile041_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile041_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile041_Wset C₀ σ X) := rfl

theorem KServer.workFn_nil (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (X : Config k M) : workFn C₀ [] X = moveCost C₀ X := by
  classical
  have hset : sharpFile041_Wset C₀ ([] : List M) X = {moveCost C₀ X} := by
    ext c
    constructor
    · rintro ⟨S, hS, rfl⟩
      simp [hS.1]
    · rintro rfl
      exact ⟨fun _ => C₀, ⟨rfl, fun j => j.elim0⟩, by simp⟩
  rw [sharpFile041_workFn_eq, hset, csInf_singleton]
end SharpFile041

-- Source: OriginalWorkFunction.lean
section SharpFile042
open scoped BigOperators

namespace KServer

theorem workFnU_rec_eq (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) X =
      workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  exact (wfU_rec_ge k hk M C₀ σ r X).imp fun i hi =>
    le_antisymm (wfU_rec_le k hk M C₀ σ r X i) hi

theorem workFnU_coalesced_nil (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (p : M) (X : Config k M) :
    workFnU (fun _ : Fin k => p) [] X = ∑ i, dist p (X i) := by
  have hperm (π : Equiv.Perm (Fin k)) :
      workFn (fun _ : Fin k => p) [] (X ∘ π) = ∑ i, dist p (X i) := by
    simpa only [workFn_nil k hk M, moveCost, Function.comp_apply] using
      Fintype.sum_equiv π (fun i => dist p (X (π i))) (fun i => dist p (X i)) (fun _ => rfl)
  simp only [workFnU, hperm, ciInf_const]

end KServer
end SharpFile042

-- Source: field/FreshVariables.lean
section SharpFile043
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem varF_algebraicIndependent : AlgebraicIndependent ℚ (@varF k M) := by
  exact (MvPolynomial.algebraicIndependent_X (Var k M) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Var k M) ℚ) (F k M))
    (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))

theorem varF_algebraicIndependent_over_complement (S : Set (Var k M)) :
    AlgebraicIndependent (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ))
      (fun i : S => varF (i : Var k M)) := by
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    ((AlgebraicIndependent.iff_adjoin_image_compl S).mp varF_algebraicIndependent).2

theorem fresh_vars_linearIndependent {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) :
    LinearIndependent
      (IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ))
      (fun i => varF (v i)) := by
  exact (varF_algebraicIndependent_over_complement (Set.range v)).linearIndependent.comp
    (fun i => ⟨v i, Set.mem_range_self i⟩)
    (fun _ _ h => hv (congrArg Subtype.val h))

theorem complement_closure_le_adjoin (S : Set (Var k M)) :
    Subfield.closure ((@varF k M) '' Sᶜ) ≤
      (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ)).toSubfield := by
  exact Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _)

theorem fresh_vars_sum_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (b : Fin N → F k M)
    (hb : ∀ i, b i ∈ Subfield.closure ((@varF k M) '' (Set.range v)ᶜ))
    (hne : ∃ i, b i ≠ 0) :
    ∑ i, varF (v i) * b i ≠ 0 := by
  intro hz
  let c : Fin N → IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ) :=
    fun i => ⟨b i, complement_closure_le_adjoin (Set.range v) (hb i)⟩
  have hsum : ∑ i, c i • varF (v i) = 0 := by
    simpa only [c, IntermediateField.smul_def, Subtype.coe_mk, smul_eq_mul, mul_comm] using hz
  have hczero := Fintype.linearIndependent_iff.mp (fresh_vars_linearIndependent v hv) c hsum
  exact hne.elim (fun i hi => hi (congrArg Subtype.val (hczero i)))

end KServerConj
end SharpFile043

-- Source: field/ConstantMatrixValuation.lean
section SharpFile044
namespace KServerConj

theorem nu_det_C {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (F k M)) (hA : A.det ≠ 0) :
    nu (((HahnSeries.C : F k M →+* K k M).mapMatrix A).det) = 0 := by
  exact (congrArg nu ((HahnSeries.C : F k M →+* K k M).map_det A).symm).trans (nu_C hA)

end KServerConj
end SharpFile044

-- Source: field/HahnCoeffSubfield.lean
section SharpFile045
namespace KServerConj

noncomputable def hahnCoeffMap {F E : Type*} [Field F] [Field E] (g : F →+* E) :
    HahnSeries ℝ F →+* HahnSeries ℝ E where
  toFun f := f.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := by
    simpa only [map_one] using (HahnSeries.map_C (Γ := ℝ) (1 : F) g)
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

@[simp] theorem hahnCoeffMap_coeff {F E : Type*} [Field F] [Field E]
    (g : F →+* E) (f : HahnSeries ℝ F) (a : ℝ) :
    (hahnCoeffMap g f).coeff a = g (f.coeff a) := rfl

noncomputable def restrictCoeffs {F : Type*} [Field F] (S : Subfield F) (f : HahnSeries ℝ F)
    (hf : ∀ a, f.coeff a ∈ S) : HahnSeries ℝ S where
  coeff a := ⟨f.coeff a, hf a⟩
  isPWO_support' := f.isPWO_support.mono fun _ ha hz => ha (Subtype.ext hz)

@[simp] theorem restrictCoeffs_map {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    hahnCoeffMap S.subtype (restrictCoeffs S f hf) = f := by
  exact HahnSeries.coeff_injective rfl

theorem coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    ∀ a, (f⁻¹).coeff a ∈ S := by
  have hmap : hahnCoeffMap S.subtype (restrictCoeffs S f hf)⁻¹ = f⁻¹ := by
    rw [map_inv₀, restrictCoeffs_map]
  exact fun a => (congrArg (fun g : HahnSeries ℝ F => g.coeff a) hmap) ▸
    (((restrictCoeffs S f hf)⁻¹).coeff a).property

end KServerConj
end SharpFile045

-- Source: field/FreeOfLaws.lean
section SharpFile046
namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem freeOf_zero (S : Set (Var k M)) : FreeOf S (0 : K k M) := by
  exact fun _ => Subfield.zero_mem _

theorem freeOf_single (S : Set (Var k M)) (a : ℝ) (c : F k M)
    (hc : c ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)) :
    FreeOf S (HahnSeries.single a c) := by
  intro b
  rw [HahnSeries.coeff_single]
  exact ite_mem.mpr ⟨fun _ => hc, fun _ => Subfield.zero_mem _⟩

theorem freeOf_zp (S : Set (Var k M)) (a : ℝ) : FreeOf S (zp a : K k M) := by
  exact freeOf_single S a 1 (Subfield.one_mem _)

theorem freeOf_one (S : Set (Var k M)) : FreeOf S (1 : K k M) := by
  exact freeOf_single S 0 1 (Subfield.one_mem _)

theorem freeOf_coef (S : Set (Var k M)) (v : Var k M) (hv : v ∉ S) :
    FreeOf S (coef v) := by
  exact freeOf_single S 0 (varF v) (Subfield.subset_closure ⟨v, hv, rfl⟩)

theorem freeOf_add {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f + g) := by
  simpa only [FreeOf, HahnSeries.coeff_add] using
    fun a => Subfield.add_mem _ (hf a) (hg a)

theorem freeOf_neg {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S (-f) := by
  simpa only [FreeOf, HahnSeries.coeff_neg] using
    fun a => Subfield.neg_mem _ (hf a)

theorem freeOf_mul {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f * g) := by
  intro a
  rw [HahnSeries.coeff_mul]
  exact Subfield.sum_mem _ fun ij _ => Subfield.mul_mem _ (hf ij.1) (hg ij.2)

theorem freeOf_inv {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S f⁻¹ := by
  exact coeff_inv_mem_subfield _ f hf

noncomputable def freeOfSubfield (S : Set (Var k M)) : Subfield (K k M) where
  carrier := FreeOf S
  zero_mem' := freeOf_zero S
  one_mem' := freeOf_one S
  add_mem' := freeOf_add
  mul_mem' := freeOf_mul
  neg_mem' := freeOf_neg
  inv_mem' := fun _ hf => freeOf_inv hf

theorem freeOf_div {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f / g) := by
  exact (freeOfSubfield S).div_mem hf hg

theorem freeOf_sum {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∑ i ∈ s, f i) := by
  exact (freeOfSubfield S).sum_mem hf

theorem freeOf_prod {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∏ i ∈ s, f i) := by
  exact (freeOfSubfield S).prod_mem hf

theorem freeOf_mono {S T : Set (Var k M)} {f : K k M} (hST : S ⊆ T)
    (hf : FreeOf T f) : FreeOf S f := by
  exact fun a => Subfield.closure_mono (Set.image_mono (Set.compl_subset_compl.mpr hST)) (hf a)

end KServerConj
end SharpFile046

-- Source: field/FreeOfMatrix.lean
section SharpFile047
namespace KServerConj

theorem freeOf_det {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (Var k M)} (A : Matrix ι ι (K k M)) (hA : ∀ i j, FreeOf S (A i j)) :
    FreeOf S A.det := by
  let B : Matrix ι ι (freeOfSubfield S) := fun i j => ⟨A i j, hA i j⟩
  exact ((freeOfSubfield S).subtype.map_det B) ▸ B.det.property

end KServerConj
end SharpFile047

-- Source: field/Initialization.lean
section SharpFile048
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem gamma_det_ne_zero (x : Fin k → M) (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j))).det ≠ 0 := by
  let ρ : Fin k × Fin k → Var k M := fun ij => Sum.inl (ij.1, x ij.2)
  have hρ : Function.Injective ρ := fun a b h =>
    let h' : (a.1, x a.2) = (b.1, x b.2) := Sum.inl.inj h
    Prod.ext (congrArg (fun z : Fin k × M => z.1) h')
      (hx (congrArg (fun z : Fin k × M => z.2) h'))
  have hAI := (@varF_algebraicIndependent k M).comp ρ hρ
  have hne := (map_ne_zero_iff (MvPolynomial.aeval ((@varF k M) ∘ ρ))
    (algebraicIndependent_iff_injective_aeval.mp hAI)).mpr
      (Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := ℚ))
  simpa [AlgHom.map_det, Matrix.mvPolynomialX, Matrix.map, ρ] using hne

theorem nu_gamma_det (x : Fin k → M) (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det) = 0 := by
  exact nu_det_C (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j)))
    (gamma_det_ne_zero x hx)

theorem weighted_gamma_det_valuation (w : M → ℝ) (x : Fin k → M)
    (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det) =
      ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  have hfactor :
      (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det =
        (∏ j, (zp (w (x j)) : K k M)) *
          (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det := by
    simpa only [Matrix.of_apply, mul_comm] using
      Matrix.det_mul_row (fun j => (zp (w (x j)) : K k M))
        (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)))
  rw [hfactor, ← zp_sum Finset.univ (fun j => w (x j)), nu_mul, nu_zp,
    nu_gamma_det x hx, add_zero]

theorem initCols_colDet_valuation_of_uniform_dist [PseudoMetricSpace M]
    (s : Fin k → M) (w : M → ℝ) (hd : ∀ i y, dist (s i) y = w y)
    (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols s) x) = ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  simpa only [colDet, initCols, hd] using weighted_gamma_det_valuation w x hx

theorem initCols_coalesced_valuation [PseudoMetricSpace M]
    (p : M) (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols (fun _ : Fin k => p)) x) =
      ((∑ j, dist p (x j) : ℝ) : WithTop ℝ) := by
  exact initCols_colDet_valuation_of_uniform_dist (fun _ => p) (dist p) (fun _ _ => rfl) x hx

theorem initCols_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (y : M) (i : Fin k) : FreeOf S (initCols s y i) := by
  exact freeOf_mul (freeOf_coef S (Sum.inl (i, y)) (hS i y))
    (freeOf_zp S (dist (s i) y))

theorem colDet_freeOf (S : Set (Var k M)) (q : M → Fin k → K k M)
    (x : Fin k → M) (hq : ∀ i j, FreeOf S (q (x j) i)) : FreeOf S (colDet q x) := by
  exact freeOf_det (Matrix.of fun i j => q (x j) i) hq

theorem initCols_colDet_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (x : Fin k → M) : FreeOf S (colDet (initCols s) x) := by
  exact colDet_freeOf S (initCols s) x (fun i j => initCols_freeOf S hS s (x j) i)

end KServerConj
end SharpFile048

-- Source: field/FreshCoefficientValuation.lean
section SharpFile049
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem coeff_fresh_term (v : Var k M) (a b : ℝ) (f : K k M) :
    (coef v * zp a * f).coeff b = varF v * f.coeff (b - a) := by
  simp only [mul_assoc, coef, HahnSeries.C_apply, zp, HahnSeries.coeff_single_mul,
    one_mul, sub_zero]

theorem fresh_sum_coeff_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) (b : ℝ)
    (hne : ∃ i, (f i).coeff (b - a i) ≠ 0) :
    (∑ i, coef (v i) * zp (a i) * f i).coeff b ≠ 0 := by
  simpa only [HahnSeries.coeff_sum, coeff_fresh_term] using
    fresh_vars_sum_ne_zero v hv (fun i => (f i).coeff (b - a i))
      (fun i => hf i (b - a i)) hne

theorem nu_fresh_sum_le_of_ne {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ)
    (j : Fin N) (hj : f j ≠ 0) :
    nu (∑ i, coef (v i) * zp (a i) * f i) ≤ (a j : WithTop ℝ) + nu (f j) := by
  have hcoeff := fresh_sum_coeff_ne_zero v hv f hf a (a j + (f j).order)
    ⟨j, by simpa only [add_sub_cancel_left] using (HahnSeries.coeff_order_eq_zero.not.mpr hj)⟩
  simpa only [nu, HahnSeries.addVal_apply_of_ne hj, ← WithTop.coe_add] using
    (HahnSeries.addVal_le_of_coeff_ne_zero hcoeff)

theorem fresh_coefficients_no_cancellation {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) :
    nu (∑ i, coef (v i) * zp (a i) * f i) =
      Finset.univ.inf (fun i => (a i : WithTop ℝ) + nu (f i)) := by
  apply le_antisymm
  · refine Finset.le_inf ?_
    intro j _
    exact (eq_or_ne (f j) 0).elim
      (fun hj => by simp only [hj, nu_zero, WithTop.add_top, le_top])
      (nu_fresh_sum_le_of_ne v hv f hf a j)
  · exact nu_sum_ge _ _ (fun i => by
      simpa only [nu_fresh_term] using
        (Finset.inf_le (f := fun i => (a i : WithTop ℝ) + nu (f i)) (Finset.mem_univ i)))

end KServerConj
end SharpFile049

-- Source: field/RequestTuples.lean
section SharpFile050
namespace KServerConj

theorem colDet_eq_zero_of_not_injective {k : ℕ} {M : Type*}
    (q : M → Fin k → K k M) (x : Fin k → M) (hx : ¬ Function.Injective x) :
    colDet q x = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun a => congrArg (fun y => q y a) hij)

theorem update_injective_of_not_mem_range {ι M : Type*} [DecidableEq ι]
    (x : ι → M) (hx : Function.Injective x) (r : M) (hr : r ∉ Set.range x) (i : ι) :
    Function.Injective (Function.update x i r) := by
  intro a b hab
  by_cases ha : a = i
  · have hb : b = i := Classical.byContradiction fun hb => hr
      ⟨b, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab.symm⟩
    exact ha.trans hb.symm
  · have hb : b ≠ i := fun hb => hr
      ⟨a, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab⟩
    exact hx (by simpa only [Function.update_apply, ha, hb, if_false] using hab)

end KServerConj
end SharpFile050

-- Source: field/RequestInvariant.lean
section SharpFile051
open scoped BigOperators

namespace KServerConj

theorem colDet_rowReplace_eq_sum {n : ℕ} {M : Type*}
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (x : Fin (n + 1) → M) (r : M) (hr : q r = Pi.single 0 1) :
    colDet (rowReplace q δ) x =
      ∑ i, δ (x i) * colDet q (Function.update x i r) := by
  exact KServerAlgebra.det_rowReplace_column_family q δ x r hr

theorem fresh_rowReplace_valuation_eq_inf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
        nu (colDet q (Function.update x i r))) := by
  have hv : Function.Injective (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) :=
    fun _ _ h => hx (congrArg (fun p : ℕ × M => p.2) (Sum.inr.inj h))
  have hsubset :
      Set.range (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) ⊆
        Set.range (fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) :=
    fun _ ⟨i, hi⟩ => ⟨x i, hi⟩
  exact (congrArg nu (colDet_rowReplace_eq_sum q
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y)) x r hr)).trans
    (fresh_coefficients_no_cancellation
      (fun i => (Sum.inr (t, x i) : Var (n + 1) M)) hv
      (fun i => colDet q (Function.update x i r))
      (fun i => freeOf_mono hsubset (hfree (Function.update x i r)))
      (fun i => dist r (x i)))

theorem exists_injective_update_le {ι M : Type*} [DecidableEq ι] [PseudoMetricSpace M]
    (x : ι → M) (hx : Function.Injective x) (r : M)
    (w : (ι → M) → ℝ) (b : ℝ)
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b) (hmono : w x ≤ b) :
    ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b := by
  by_cases hrange : r ∈ Set.range x
  · exact hrange.elim (fun j hj =>
      let hu : Function.update x j r = x := Function.update_eq_self_iff.mpr hj.symm
      ⟨j, hu.symm ▸ hx, by simpa only [hu, hj, dist_self, add_zero] using hmono⟩)
  · exact hge.elim (fun i hi =>
      ⟨i, update_injective_of_not_mem_range x hx r hrange i, hi⟩)

theorem determinant_cost_inf_eq {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b)
    (hmono : w x ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := exists_injective_update_le x hx r w b hge hmono
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    exact (em (Function.Injective (Function.update x i r))).elim
      (fun hi => by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr (hle i)))
      (fun hi => by
        simp only [colDet_eq_zero_of_not_injective q _ hi, nu_zero, WithTop.add_top, le_top])

theorem request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : q r = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      (w' x : WithTop ℝ) := by
  exact (fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (determinant_cost_inf_eq q r w (w' x) hrep x hx
      (hrec_le x hx) (hrec_ge x hx) (hmono x hx))

theorem rowReplace_det_freeOf {n : ℕ} {M : Type*} (S : Set (Var (n + 1) M))
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (r : M) (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hδ : ∀ y : M, FreeOf S (δ y)) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q δ) x) := by
  exact (colDet_rowReplace_eq_sum q δ x r hr).symm ▸
    freeOf_sum Finset.univ (fun i => δ (x i) * colDet q (Function.update x i r))
      (fun i _ => freeOf_mul (hδ (x i)) (hfree (Function.update x i r)))

theorem fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M)) (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact rowReplace_det_freeOf S q _ r hr hfree
    (fun y => freeOf_mul (freeOf_coef S (Sum.inr (t, y)) (hS y)) (freeOf_zp S (dist r y))) x

theorem colDet_normalize_eq {k : ℕ} {M : Type*}
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) (x : Fin k → M) :
    colDet (fun y => B.mulVec (q y)) x = colDet q x := by
  exact KServerAlgebra.det_normalized_column_family B hB q x

theorem normalized_request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : B.mulVec (q r) = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (w' x : WithTop ℝ) := by
  exact request_representation_step (fun y => B.mulVec (q y)) r t w w' hr
    (fun y hy => (congrArg nu (colDet_normalize_eq B hB q y)).trans (hrep y hy))
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y)
    hrec_le hrec_ge hmono x hx

theorem normalized_fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : B.mulVec (q r) = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact fresh_rowReplace_det_freeOf S (fun y => B.mulVec (q y)) r t hr
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y) hS x

end KServerConj
end SharpFile051

-- Source: Normalization.lean
section SharpFile052
open scoped BigOperators

namespace KServerAlgebra

theorem exists_nonsingular_matrix_with_first_column
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      A.det ≠ 0 ∧ (fun r => A r 0) = v := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine ⟨((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateCol j v).submatrix
    id (Equiv.swap 0 j), ?_, ?_⟩
  · rw [Matrix.det_permute']
    apply mul_ne_zero
    · exact ((Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) j)).isUnit.map
        (Int.castRingHom K)).ne_zero
    · simpa [← Matrix.cramer_apply] using hj
  · exact funext (fun r => by simp [Matrix.submatrix])

theorem exists_nonsingular_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      T.det ≠ 0 ∧ T.mulVec v = Pi.single 0 1 := by
  obtain ⟨A, hA, hcol⟩ := exists_nonsingular_matrix_with_first_column v hv
  refine ⟨A⁻¹, (A.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr hA)).ne_zero, ?_⟩
  have hvec : A.mulVec (Pi.single 0 1) = v := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply'] using hcol
  rw [← hvec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]

theorem exists_det_one_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 2) → K) (hv : v ≠ 0) :
    ∃ B : Matrix (Fin (n + 2)) (Fin (n + 2)) K,
      B.det = 1 ∧ B.mulVec v = Pi.single 0 1 := by
  obtain ⟨T, hT, hTv⟩ := exists_nonsingular_normalizer v hv
  refine ⟨T.updateRow 1 (T.det⁻¹ • T 1), ?_, ?_⟩
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, inv_mul_cancel₀ hT]
  · have hrow : dotProduct (T 1) v = 0 := by
      simpa [Matrix.mulVec] using congrFun hTv 1
    simp [Matrix.updateRow_mulVec, smul_dotProduct, hrow, hTv]

end KServerAlgebra
end SharpFile052

-- Source: representation/InitialMatrix.lean
section SharpFile053
open scoped BigOperators
open KServerConj

namespace KServerRepresentation

noncomputable def initialColumns (k : ℕ) (N : Type) [MetricSpace N] (p : N) :
    (N × Fin k) → Fin k → K k (N × Fin k) :=
  fun y i => coef (Sum.inl (i, y)) * zp (dist p y.1)

theorem initial_represents (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (p : N) (x : Fin k → N × Fin k) (hx : Function.Injective x) :
    nu (colDet (initialColumns k N p) x) =
      (KServer.workFnU (fun _ : Fin k => p) [] (Prod.fst ∘ x) : WithTop ℝ) := by
  simpa only [KServer.workFnU_coalesced_nil k hk N p, Function.comp_apply, colDet, initialColumns] using
    weighted_gamma_det_valuation (fun y : N × Fin k => dist p y.1) x hx

theorem initial_det_fresh (k : ℕ) (N : Type) [MetricSpace N] (p : N)
    (t : ℕ) (x : Fin k → N × Fin k) :
    FreeOf (Set.range fun y : N × Fin k => (Sum.inr (t, y) : Var k (N × Fin k)))
      (colDet (initialColumns k N p) x) := by
  have hS : ∀ (i : Fin k) (y : N × Fin k),
      (Sum.inl (i, y) : Var k (N × Fin k)) ∉
        Set.range (fun z : N × Fin k => (Sum.inr (t, z) : Var k (N × Fin k))) :=
    fun _ _ ⟨_, hz⟩ => by cases hz
  exact colDet_freeOf _ (initialColumns k N p) x (fun i j =>
    freeOf_mul (freeOf_coef _ (Sum.inl (i, x j)) (hS i (x j)))
      (freeOf_zp _ (dist p (x j).1)))

end KServerRepresentation
end SharpFile053

-- Source: representation/ProjectedRecurrence.lean
section SharpFile054
namespace KServerRepresentation

theorem projected_rec_le (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (p : N) (l : List N) (a : N × Fin k) (x : Fin k → N × Fin k) (i : Fin k) :
    KServer.workFnU (fun _ : Fin k => p) (l ++ [a.1]) (Prod.fst ∘ x) ≤
      KServer.workFnU (fun _ : Fin k => p) l (Prod.fst ∘ Function.update x i a) +
        dist a.1 (x i).1 := by
  simpa only [Function.comp_update, Function.comp_apply] using
    KServer.wfU_rec_le k hk N (fun _ => p) l a.1 (Prod.fst ∘ x) i

theorem projected_rec_ge (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (p : N) (l : List N) (a : N × Fin k) (x : Fin k → N × Fin k) :
    ∃ i, KServer.workFnU (fun _ : Fin k => p) l (Prod.fst ∘ Function.update x i a) +
      dist a.1 (x i).1 ≤ KServer.workFnU (fun _ : Fin k => p) (l ++ [a.1]) (Prod.fst ∘ x) := by
  simpa only [Function.comp_update, Function.comp_apply] using
    KServer.wfU_rec_ge k hk N (fun _ => p) l a.1 (Prod.fst ∘ x)

theorem projected_mono (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (p : N) (l : List N) (a : N × Fin k) (x : Fin k → N × Fin k) :
    KServer.workFnU (fun _ : Fin k => p) l (Prod.fst ∘ x) ≤
      KServer.workFnU (fun _ : Fin k => p) (l ++ [a.1]) (Prod.fst ∘ x) := by
  exact KServer.workFnU_mono k hk N (fun _ => p) l a.1 (Prod.fst ∘ x)

end KServerRepresentation
end SharpFile054

-- Source: representation/FreshTimes.lean
section SharpFile055
namespace KServerRepresentation

theorem request_variable_not_mem_other_time {k : ℕ} {M : Type*}
    (t u : ℕ) (htu : t ≠ u) (y : M) :
    (Sum.inr (t, y) : KServerConj.Var k M) ∉
      Set.range (fun z : M => (Sum.inr (u, z) : KServerConj.Var k M)) := by
  exact fun ⟨_, hz⟩ => htu (congrArg Prod.fst (Sum.inr.inj hz)).symm

end KServerRepresentation
end SharpFile055

-- Source: WorkFunctionRepresentation.lean
section SharpFile056
open scoped BigOperators
open KServerConj

namespace KServerRepresentation

abbrev Label (k : ℕ) (N : Type) := N × Fin k

@[reducible] noncomputable def labelSpace (k : ℕ) (N : Type) [MetricSpace N] :
    PseudoMetricSpace (Label k N) :=
  PseudoMetricSpace.induced Prod.fst inferInstance

theorem labelSpace_dist {k : ℕ} {N : Type} [MetricSpace N] (x y : Label k N) :
    @dist (Label k N) (labelSpace k N).toDist x y = dist x.1 y.1 := rfl

structure State (k : ℕ) (N : Type) [MetricSpace N] (p : N) (l : List N) where
  q : Label k N → Fin k → K k (Label k N)
  represents : ∀ x : Fin k → Label k N, Function.Injective x →
    nu (colDet q x) =
      (KServer.workFnU (fun _ : Fin k => p) l (Prod.fst ∘ x) : WithTop ℝ)
  fresh : ∀ t : ℕ, l.length < t → ∀ x : Fin k → Label k N,
    FreeOf (Set.range fun y : Label k N => (Sum.inr (t, y) : Var k (Label k N))) (colDet q x)

theorem State.column_ne_zero {k : ℕ} {N : Type} [MetricSpace N] {p : N} {l : List N}
    (s : State k N p l) (y : Label k N) : s.q y ≠ 0 := by
  let x : Fin k → Label k N := fun i => (y.1, i)
  have hx : Function.Injective x := fun _ _ h => congrArg Prod.snd h
  have hdet : colDet s.q x ≠ 0 := (nu_eq_top_iff _).not.mp
    (ne_of_eq_of_ne (s.represents x hx) WithTop.coe_ne_top)
  intro hz
  exact hdet (Matrix.det_eq_zero_of_column_eq_zero y.2 (fun i => congrFun hz i))

theorem State.represents_configuration {k : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State k N p l) (C : Fin k → N) :
    nu (colDet s.q (fun i => (C i, i))) =
      (KServer.workFnU (fun _ : Fin k => p) l C : WithTop ℝ) := by
  exact s.represents (fun i => (C i, i)) (fun _ _ h => congrArg Prod.snd h)

noncomputable def initialState (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (p : N) : State k N p [] where
  q := initialColumns k N p
  represents := initial_represents k hk N p
  fresh := fun t _ x => initial_det_fresh k N p t x

noncomputable def nextColumns {n : ℕ} {N : Type} [MetricSpace N]
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) (Label (n + 1) N)))
    (q : Label (n + 1) N → Fin (n + 1) → K (n + 1) (Label (n + 1) N))
    (r : N) (t : ℕ) : Label (n + 1) N → Fin (n + 1) → K (n + 1) (Label (n + 1) N) :=
  rowReplace (fun y => B.mulVec (q y))
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y.1))

theorem nextColumns_represents {n : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State (n + 2) N p l) (r : N)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) (Label (n + 2) N)))
    (hB : B.det = 1) (hr : B.mulVec (s.q (r, 0)) = Pi.single 0 1)
    (x : Fin (n + 2) → Label (n + 2) N) (hx : Function.Injective x) :
    nu (colDet (nextColumns B s.q r (l.length + 1)) x) =
      (KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) (Prod.fst ∘ x) : WithTop ℝ) := by
  let : PseudoMetricSpace (Label (n + 2) N) := labelSpace (n + 2) N
  exact normalized_request_representation_step B hB s.q (r, 0) (l.length + 1)
    (fun y => KServer.workFnU (fun _ : Fin (n + 2) => p) l (Prod.fst ∘ y))
    (fun y => KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) (Prod.fst ∘ y))
    hr s.represents (s.fresh _ (Nat.lt_succ_self _))
    (fun y _ i => projected_rec_le _ (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p l (r, 0) y i)
    (fun y _ => projected_rec_ge _ (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p l (r, 0) y)
    (fun y _ => projected_mono _ (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p l (r, 0) y)
    x hx

theorem nextColumns_fresh {n : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State (n + 2) N p l) (r : N)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) (Label (n + 2) N)))
    (hB : B.det = 1) (hr : B.mulVec (s.q (r, 0)) = Pi.single 0 1)
    (u : ℕ) (hu : (l ++ [r]).length < u) (x : Fin (n + 2) → Label (n + 2) N) :
    FreeOf (Set.range fun y : Label (n + 2) N =>
        (Sum.inr (u, y) : Var (n + 2) (Label (n + 2) N)))
      (colDet (nextColumns B s.q r (l.length + 1)) x) := by
  let : PseudoMetricSpace (Label (n + 2) N) := labelSpace (n + 2) N
  have htu : l.length + 1 < u := by
    simpa only [List.length_append, List.length_singleton] using hu
  exact normalized_fresh_rowReplace_det_freeOf _ B hB s.q (r, 0) (l.length + 1) hr
    (s.fresh u (Nat.lt_trans (Nat.lt_succ_self _) htu))
    (request_variable_not_mem_other_time (l.length + 1) u (Nat.ne_of_lt htu)) x

noncomputable def advanceState {n : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State (n + 2) N p l) (r : N)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) (Label (n + 2) N)))
    (hB : B.det = 1) (hr : B.mulVec (s.q (r, 0)) = Pi.single 0 1) :
    State (n + 2) N p (l ++ [r]) where
  q := nextColumns B s.q r (l.length + 1)
  represents := nextColumns_represents s r B hB hr
  fresh := nextColumns_fresh s r B hB hr

theorem State.step {n : ℕ} {N : Type} [MetricSpace N] {p : N} {l : List N}
    (s : State (n + 2) N p l) (r : N) :
    ∃ (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) (Label (n + 2) N)))
      (s' : State (n + 2) N p (l ++ [r])),
      B.det = 1 ∧ B.mulVec (s.q (r, 0)) = Pi.single 0 1 ∧
      s'.q = nextColumns B s.q r (l.length + 1) := by
  exact (KServerAlgebra.exists_det_one_normalizer (s.q (r, 0))
    (s.column_ne_zero (r, 0))).elim (fun B ⟨hB, hr⟩ =>
      ⟨B, advanceState s r B hB hr, hB, hr, rfl⟩)

theorem exists_state (n : ℕ) (N : Type) [MetricSpace N] (p : N) (l : List N) :
    Nonempty (State (n + 2) N p l) := by
  exact List.reverseRecOn (motive := fun l => Nonempty (State (n + 2) N p l)) l
    ⟨initialState (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p⟩
    (fun _ r ⟨s⟩ => (s.step r).elim (fun _ ⟨s', _, _, _⟩ => ⟨s'⟩))

end KServerRepresentation
end SharpFile056

-- Source: PotentialNormalization.lean
section SharpFile057
open scoped BigOperators

namespace KServerConj

theorem quadraticMatrix_normalize {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M]
    (B : Matrix (Fin k) (Fin k) (HahnSeries ℝ F))
    (q : M → Fin k → HahnSeries ℝ F) :
    quadraticMatrix (fun y => B.mulVec (q y)) = sym2Mat B * quadraticMatrix q := by
  funext p c
  induction c using Sym2.ind with
  | _ x y =>
    exact (congrFun ((Matrix.mulVec_smul (sym2Mat B)
      (HahnSeries.single (-dist x y) (1 : F)) (symProd (q x) (q y))).trans
        (congrArg (fun v => HahnSeries.single (-dist x y) (1 : F) • v)
          (sym2Mat_mulVec_symProd B (q x) (q y)))) p).symm

theorem minorVal_quadraticMatrix_normalize {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (B : Matrix (Fin k) (Fin k) (HahnSeries ℝ F)) (hB : B.det = 1)
    (q : M → Fin k → HahnSeries ℝ F) :
    minorVal (quadraticMatrix (fun y => B.mulVec (q y))) = minorVal (quadraticMatrix q) := by
  simpa only [quadraticMatrix_normalize, det_sym2Mat, hB, one_pow,
    AddValuation.map_one, zero_add] using minorVal_mul (sym2Mat B) (quadraticMatrix q)

theorem Psi_normalize {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) :
    Psi (fun y => B.mulVec (q y)) = Psi q := by
  exact minorVal_quadraticMatrix_normalize B hB q

end KServerConj
end SharpFile057

-- Source: PotentialFiniteness.lean
section SharpFile058
open scoped BigOperators

namespace KServerConj

theorem quadraticMatrix_selected_det_ne_zero {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M)
    (hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0) :
    ((quadraticMatrix q).submatrix id (Sym2.map x)).det ≠ 0 := by
  rw [quadraticMatrix_submatrix, Matrix.det_mul_row, det_sym2Mat]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ =>
    HahnSeries.single_ne_zero one_ne_zero) (pow_ne_zero _ hdet)

theorem minorVal_quadraticMatrix_ne_top {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M)
    (hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0) :
    minorVal (quadraticMatrix q) ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (HahnSeries.orderTop_ne_top.mpr (quadraticMatrix_selected_det_ne_zero q x hdet))
    (minorVal_le_tuple (quadraticMatrix q) (Sym2.map x))

theorem exists_quadratic_minorVal {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M)
    (hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0) :
    ∃ c : ℝ, minorVal (quadraticMatrix q) = (c : WithTop ℝ) := by
  exact ⟨(minorVal (quadraticMatrix q)).untop (minorVal_quadraticMatrix_ne_top q x hdet),
    (WithTop.coe_untop _ _).symm⟩

theorem exists_tail_quadratic_minorVal {F : Type*} [Field F]
    {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (x : Fin (n + 1) → M)
    (hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0) :
    ∃ c : ℝ, minorVal (quadraticMatrix (fun y => Fin.tail (q y))) = (c : WithTop ℝ) := by
  exact (DetValuationMilestone.exists_nonzero_projected_minor
    (Matrix.of fun i y => q y i) x hdet).elim (fun y hy =>
      exists_quadratic_minorVal (fun y => Fin.tail (q y)) y hy)

theorem exists_quadratic_and_tail_minorVal {F : Type*} [Field F]
    {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (x : Fin (n + 1) → M)
    (hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0) :
    ∃ c d : ℝ,
      minorVal (quadraticMatrix q) = (c : WithTop ℝ) ∧
      minorVal (quadraticMatrix (fun y => Fin.tail (q y))) = (d : WithTop ℝ) := by
  exact (exists_quadratic_minorVal q x hdet).elim (fun c hc =>
    (exists_tail_quadratic_minorVal q x hdet).elim (fun d hd => ⟨c, d, hc, hd⟩))

end KServerConj

namespace KServerRepresentation

open KServerConj

theorem State.configuration_det_ne_zero {k : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State k N p l) (C : Fin k → N) :
    (Matrix.of fun i j => s.q (C j, j) i).det ≠ 0 := by
  exact (nu_eq_top_iff _).not.mp
    (ne_of_eq_of_ne (s.represents_configuration C) WithTop.coe_ne_top)

theorem State.normalized_configuration_det_ne_zero {k : ℕ} {N : Type} [MetricSpace N]
    {p : N} {l : List N} (s : State k N p l) (C : Fin k → N)
    (B : Matrix (Fin k) (Fin k) (K k (Label k N))) (hB : B.det = 1) :
    (Matrix.of fun i j => B.mulVec (s.q (C j, j)) i).det ≠ 0 := by
  exact ne_of_eq_of_ne (colDet_normalize_eq B hB s.q (fun i => (C i, i)))
    (s.configuration_det_ne_zero C)

theorem State.potential_ne_top {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State k N p l) :
    letI : PseudoMetricSpace (Label k N) := labelSpace k N
    minorVal (quadraticMatrix s.q) ≠ ⊤ := by
  let : PseudoMetricSpace (Label k N) := labelSpace k N
  exact minorVal_quadraticMatrix_ne_top s.q (fun i => (p, i))
    (s.configuration_det_ne_zero (fun _ => p))

noncomputable def State.potential {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State k N p l) : ℝ :=
  letI : PseudoMetricSpace (Label k N) := labelSpace k N
  (minorVal (quadraticMatrix s.q)).untop s.potential_ne_top

theorem State.potential_spec {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State k N p l) :
    letI : PseudoMetricSpace (Label k N) := labelSpace k N
    minorVal (quadraticMatrix s.q) = (s.potential : WithTop ℝ) := by
  exact (WithTop.coe_untop _ _).symm

theorem State.normalized_potential_spec {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State k N p l)
    (B : Matrix (Fin k) (Fin k) (K k (Label k N))) (hB : B.det = 1) :
    letI : PseudoMetricSpace (Label k N) := labelSpace k N
    minorVal (quadraticMatrix (fun y => B.mulVec (s.q y))) = (s.potential : WithTop ℝ) := by
  let : PseudoMetricSpace (Label k N) := labelSpace k N
  exact (minorVal_quadraticMatrix_normalize B hB s.q).trans s.potential_spec

theorem State.normalized_potentials {n : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State (n + 1) N p l)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) (Label (n + 1) N)))
    (hB : B.det = 1) :
    letI : PseudoMetricSpace (Label (n + 1) N) := labelSpace (n + 1) N
    ∃ c d : ℝ,
      minorVal (quadraticMatrix (fun y => B.mulVec (s.q y))) = (c : WithTop ℝ) ∧
      minorVal (quadraticMatrix (fun y => Fin.tail (B.mulVec (s.q y)))) = (d : WithTop ℝ) := by
  let : PseudoMetricSpace (Label (n + 1) N) := labelSpace (n + 1) N
  exact exists_quadratic_and_tail_minorVal (fun y => B.mulVec (s.q y)) (fun i => (p, i))
    (s.normalized_configuration_det_ne_zero (fun _ => p) B hB)

end KServerRepresentation
end SharpFile058

-- Source: PotentialGrowth.lean
section SharpFile059
open scoped BigOperators

namespace KServerConj

theorem weightedColumns_rescale {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r y : M) :
    HahnSeries.single (dist r y) (1 : F) • (fun i => weightedColumns q r i y) = q y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, weightedColumns, ← mul_assoc,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one]

theorem tupleMinorVal_eq_minorVal {F I J : Type*} [Field F]
    [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    DetValuationMilestone.tupleMinorVal (HahnSeries.addVal ℝ F) G = minorVal G := by
  exact (DetValuationMilestone.tupleMinorVal_eq_embeddingMinorVal
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) G).trans
      (minorVal_eq_embeddingMinorVal G).symm

theorem projected_weighted_growth_of_cramer_min
    {F : Type*} [Field F] {n : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → HahnSeries ℝ F) (r : M) (x : Fin (n + 1) → M)
    (δ β : ℝ)
    (hδ : HahnSeries.addVal ℝ F (Matrix.of fun i j => q (x j) i).det = (δ : WithTop ℝ))
    (hβ : (Finset.univ.inf fun i => HahnSeries.addVal ℝ F
      (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
        HahnSeries.single (dist r (x i)) (1 : F))) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  have hdet : (Matrix.of fun i j => q (x j) i).det ≠ 0 :=
    HahnSeries.orderTop_ne_top.mp (ne_of_eq_of_ne hδ WithTop.coe_ne_top)
  obtain ⟨δ', α', a, b, hδ', hα', ha, hb, hgrow⟩ :=
    DetValuationMilestone.canonical_projected_minValue_growth
      (HahnSeries.addVal ℝ F) (fun _ => HahnSeries.orderTop_eq_top)
      (fun f g => AddValuation.map_mul _ f g)
      (fun f g => AddValuation.map_add _ f g)
      (Matrix.of fun i j => q (x j) i) (weightedColumns q r) x
      (fun i => HahnSeries.single (dist r (x i)) (1 : F))
      (fun i => (weightedColumns_rescale q r (x i)).symm) hdet
  exact ⟨a, b,
    (tupleMinorVal_eq_minorVal (weightedColumns q r)).symm.trans ha,
    (tupleMinorVal_eq_minorVal ((weightedColumns q r).submatrix Fin.succ id)).symm.trans hb,
    by simpa only [WithTop.coe_inj.mp (hδ'.symm.trans hδ),
      WithTop.coe_inj.mp (hα'.symm.trans hβ)] using hgrow⟩

theorem fresh_rowReplace_valuation_eq_cramerMin {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => nu
        (((Matrix.of fun a b => q (x b) a).updateCol i (Pi.single 0 1)).det *
          zp (dist r (x i)))) := by
  exact (fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (Finset.inf_congr rfl fun i _ => by
      simp only [← hr, KServerAlgebra.updateCol_column_family, nu_mul, nu_zp, colDet,
        add_comm])

theorem request_projected_minor_growth {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) (δ β : ℝ)
    (hδ : nu (colDet q x) = (δ : WithTop ℝ))
    (hβ : nu (colDet (rowReplace q
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (β : WithTop ℝ)) :
    ∃ a b : ℝ,
      minorVal (weightedColumns q r) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns q r).submatrix Fin.succ id) = (b : WithTop ℝ) ∧
      β - δ ≤ b - a := by
  exact projected_weighted_growth_of_cramer_min q r x δ β hδ
    ((fresh_rowReplace_valuation_eq_cramerMin q r t hr hfree x hx).symm.trans hβ)

end KServerConj
end SharpFile059

-- Source: RepresentationGrowth.lean
section SharpFile060
namespace KServerRepresentation

open KServerConj

theorem State.projected_request_growth {n : ℕ} {N : Type}
    [MetricSpace N] [Fintype N] {p : N} {l : List N}
    (s : State (n + 2) N p l) (r : N)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) (Label (n + 2) N)))
    (hB : B.det = 1) (hr : B.mulVec (s.q (r, 0)) = Pi.single 0 1)
    (x : Fin (n + 2) → Label (n + 2) N) (hx : Function.Injective x) :
    letI : PseudoMetricSpace (Label (n + 2) N) := labelSpace (n + 2) N
    ∃ a b : ℝ,
      minorVal (weightedColumns (fun y => B.mulVec (s.q y)) (r, 0)) = (a : WithTop ℝ) ∧
      minorVal ((weightedColumns (fun y => B.mulVec (s.q y)) (r, 0)).submatrix Fin.succ id) =
        (b : WithTop ℝ) ∧
      KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) (Prod.fst ∘ x) -
        KServer.workFnU (fun _ : Fin (n + 2) => p) l (Prod.fst ∘ x) ≤ b - a := by
  let : PseudoMetricSpace (Label (n + 2) N) := labelSpace (n + 2) N
  exact request_projected_minor_growth (fun y => B.mulVec (s.q y)) (r, 0) (l.length + 1)
    hr (fun y => (colDet_normalize_eq B hB s.q y).symm ▸
      s.fresh (l.length + 1) (Nat.lt_succ_self _) y) x hx
    (KServer.workFnU (fun _ : Fin (n + 2) => p) l (Prod.fst ∘ x))
    (KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) (Prod.fst ∘ x))
    ((congrArg nu (colDet_normalize_eq B hB s.q x)).trans (s.represents x hx))
    (nextColumns_represents s r B hB hr x hx)

end KServerRepresentation
end SharpFile060

-- Source: PotentialStep.lean
section SharpFile061
namespace KServerRepresentation

open KServerConj

theorem State.step_potential_growth {n : ℕ} {N : Type}
    [MetricSpace N] [Fintype N] {p : N} {l : List N}
    (s : State (n + 2) N p l) (r : N) (C : Fin (n + 2) → N) :
    ∃ s' : State (n + 2) N p (l ++ [r]),
      KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) C -
        KServer.workFnU (fun _ : Fin (n + 2) => p) l C ≤ s'.potential - s.potential := by
  classical
  let : PseudoMetricSpace (Label (n + 2) N) := labelSpace (n + 2) N
  obtain ⟨B, s', hB, hr, hs'⟩ := s.step r
  obtain ⟨a, b, ha, hb, hg⟩ := s.projected_request_growth r B hB hr
    (fun i => (C i, i)) (fun _ _ h => congrArg Prod.snd h)
  obtain ⟨_, c, _, hc⟩ := s.normalized_potentials B hB
  have hold := quadraticMatrix_old_bound_finite (fun y => B.mulVec (s.q y)) (r, 0)
    hr a c ha hc
  have hold_real : s.potential ≤ a + c := by
    simpa only [s.normalized_potential_spec B hB, WithTop.coe_le_coe] using hold
  have hnew := quadratic_new_potential_lower_bound (fun y => B.mulVec (s.q y)) (r, 0)
    (fun y => coef (Sum.inr (l.length + 1, y)) * zp (dist r y.1))
    (fun y => by
      change nu (coef (Sum.inr (l.length + 1, y)) * zp (dist r y.1)) =
        (dist r y.1 : WithTop ℝ)
      simp only [nu_mul, nu_coef, nu_zp, zero_add])
    b c hb hc
  have hnew_real : b + c ≤ s'.potential := by
    change ((b + c : ℝ) : WithTop ℝ) ≤
      minorVal (quadraticMatrix (nextColumns B s.q r (l.length + 1))) at hnew
    rw [← hs', s'.potential_spec] at hnew
    exact WithTop.coe_le_coe.mp hnew
  change KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) C -
    KServer.workFnU (fun _ : Fin (n + 2) => p) l C ≤ b - a at hg
  exact ⟨s', by linarith only [hg, hold_real, hnew_real]⟩

end KServerRepresentation
end SharpFile061

-- Source: PotentialEndpoints.lean
section SharpFile062
open scoped BigOperators

namespace KServerConj

theorem single_add_one {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (a + b) (1 : F) : HahnSeries ℝ F) =
      HahnSeries.single a (1 : F) * HahnSeries.single b (1 : F) := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F)) (s := 1)).symm

theorem single_sum_one {F ι : Type*} [Field F] (s : Finset ι) (a : ι → ℝ) :
    (HahnSeries.single (∑ i ∈ s, a i) (1 : F) : HahnSeries ℝ F) =
      ∏ i ∈ s, HahnSeries.single (a i) (1 : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, HahnSeries.single_zero_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, single_add_one, ih]

theorem quadraticMatrix_selected_det {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      HahnSeries.single (∑ c, negPairDist x c) (1 : F) *
        (Matrix.of (fun i j => q (x j) i)).det ^ (k + 1) := by
  rw [quadraticMatrix_submatrix]
  rw [Matrix.det_mul_row (fun c => HahnSeries.single (negPairDist x c) (1 : F))
    (sym2Mat (Matrix.of (fun i j => q (x j) i)))]
  rw [det_sym2Mat, ← single_sum_one]

theorem quadraticMatrix_selected_valuation {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      ((∑ c, negPairDist x c) + ((k : ℝ) + 1) * δ : ℝ) := by
  rw [quadraticMatrix_selected_det, AddValuation.map_mul, AddValuation.map_pow, hD]
  rw [show HahnSeries.addVal ℝ F
      (HahnSeries.single (∑ c, negPairDist x c) (1 : F)) =
      (((∑ c, negPairDist x c) : ℝ) : WithTop ℝ) from HahnSeries.orderTop_single one_ne_zero]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

theorem negPairDist_nonpos {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) (c : Sym2 (Fin k)) : negPairDist x c ≤ 0 := by
  induction c using Sym2.ind with
  | _ i j => exact neg_nonpos.mpr dist_nonneg

theorem minorVal_quadratic_le {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((((k : ℝ) + 1) * δ : ℝ) : WithTop ℝ) := by
  exact (minorVal_le_tuple (quadraticMatrix q) (Sym2.map x)).trans
    ((quadraticMatrix_selected_valuation q x δ hD).le.trans
      (WithTop.coe_le_coe.mpr (add_le_of_nonpos_left
        (Finset.sum_nonpos fun c _ => negPairDist_nonpos x c))))

end KServerConj
end SharpFile062

-- Source: Theorems/Thm_KServer_workFn_approx_offlineCost.lean
section SharpFile063
open KServer

private theorem sharpFile063_moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem sharpFile063_moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem sharpFile063_moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sharpFile063_sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def sharpFile063_Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile063_workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (sharpFile063_Wset C₀ σ X) := rfl

private theorem sharpFile063_Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (sharpFile063_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile063_sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile063_Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (sharpFile063_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile063_moveCost_nonneg _ _
  have h2 := sharpFile063_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile063_wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [sharpFile063_workFn_eq]
  refine le_csInf (sharpFile063_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile063_moveCost_nonneg _ _
  have h2 := sharpFile063_moveCost_nonneg (S σ.length) X
  linarith

private theorem sharpFile063_wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [sharpFile063_workFn_eq, sharpFile063_workFn_eq]
  have hkey : ∀ c ∈ sharpFile063_Wset C₀ σ Y, sInf (sharpFile063_Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ sharpFile063_Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (sharpFile063_Wset_bdd C₀ σ X) hmem
    have h2 := sharpFile063_moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (sharpFile063_Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

private theorem sharpFile063_wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [sharpFile063_workFn_eq, sharpFile063_workFn_eq]
  refine le_csInf (sharpFile063_Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ sharpFile063_Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (sharpFile063_Wset_bdd C₀ σ X) hmem
  have h2 := sharpFile063_moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sharpFile063_sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

private theorem sharpFile063_wf_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (sharpFile063_wf_mono k hk M C₀ σ r X)
  rw [sharpFile063_workFn_eq, sharpFile063_workFn_eq]
  refine csInf_le_csInf (sharpFile063_Wset_bdd C₀ (σ ++ [r]) X) (sharpFile063_Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, sharpFile063_moveCost_self]
  ring

private theorem sharpFile063_moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sharpFile063_sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

theorem KServer.workFn_approx_offlineCost (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, workFn C₀ σ X ≤ offlineCost C₀ σ + ε := by
  classical
  set T : Set ℝ := {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} with hT
  have hTne : T.Nonempty := by
    obtain ⟨S, hS⟩ := sharpFile063_sched_exists k hk M C₀ σ
    exact ⟨_, ⟨S, hS, rfl⟩⟩
  have hoff : offlineCost C₀ σ = sInf T := rfl
  have hlt : sInf T < offlineCost C₀ σ + ε := by rw [hoff]; linarith
  obtain ⟨c, hcT, hclt⟩ := exists_lt_of_csInf_lt hTne hlt
  obtain ⟨S, hS, rfl⟩ := hcT
  refine ⟨S σ.length, ?_⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) (S σ.length) ∈ sharpFile063_Wset C₀ σ (S σ.length) := ⟨S, hS, rfl⟩
  have h1 : workFn C₀ σ (S σ.length)
      ≤ (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) (S σ.length) := by
    rw [sharpFile063_workFn_eq]; exact csInf_le (sharpFile063_Wset_bdd C₀ σ (S σ.length)) hmem
  rw [sharpFile063_moveCost_self] at h1
  linarith
end SharpFile063

-- Source: WorkFunctionBounds.lean
section SharpFile064
namespace KServer

theorem workFnU_le_workFn {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFn C₀ σ X := by
  exact ciInf_le (Finite.bddBelow_range
    (fun π : Equiv.Perm (Fin k) => workFn C₀ σ (X ∘ π))) (Equiv.refl (Fin k))

theorem le_offlineCost_of_le_workFnU {k : ℕ} {M : Type} [MetricSpace M]
    (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) (Φ c : ℝ) (hc : 0 < c)
    (hΦ : ∀ X : Config k M, Φ ≤ c * workFnU C₀ σ X) :
    Φ ≤ c * offlineCost C₀ σ := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / c) (div_pos hε hc)
  calc
    Φ ≤ c * workFnU C₀ σ X := hΦ X
    _ ≤ c * (offlineCost C₀ σ + ε / c) :=
      mul_le_mul_of_nonneg_left ((workFnU_le_workFn C₀ σ X).trans hX) hc.le
    _ = c * offlineCost C₀ σ + ε := by
      rw [mul_add, mul_comm c (ε / c), div_mul_cancel₀ ε hc.ne']

end KServer
end SharpFile064

-- Source: StatePotentialBounds.lean
section SharpFile065
open scoped BigOperators

namespace KServerRepresentation

open KServerConj

theorem State.potential_le_workFnU {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    {p : N} {l : List N} (s : State k N p l) (C : Fin k → N) :
    s.potential ≤ ((k : ℝ) + 1) * KServer.workFnU (fun _ : Fin k => p) l C := by
  classical
  let : PseudoMetricSpace (Label k N) := labelSpace k N
  have h := minorVal_quadratic_le s.q (fun i => (C i, i))
    (KServer.workFnU (fun _ : Fin k => p) l C) (s.represents_configuration C)
  simpa only [s.potential_spec, WithTop.coe_le_coe] using h

theorem State.potential_le_offlineCost {k : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    (hk : 1 ≤ k) {p : N} {l : List N} (s : State k N p l) :
    s.potential ≤ ((k : ℝ) + 1) * KServer.offlineCost (fun _ : Fin k => p) l := by
  exact KServer.le_offlineCost_of_le_workFnU hk _ _ _ _
    (by positivity) s.potential_le_workFnU

end KServerRepresentation
end SharpFile065

-- Source: PotentialInitial.lean
section SharpFile066
open scoped BigOperators

namespace KServerConj

theorem symProd_valuation_lower_bound {F : Type*} [Field F] {k : ℕ}
    (a b : Fin k → HahnSeries ℝ F) (α β : ℝ)
    (ha : ∀ i, (α : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (a i))
    (hb : ∀ i, (β : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (b i))
    (p : Sym2 (Fin k)) :
    ((α + β : ℝ) : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (symProd a b p) := by
  induction p using Sym2.ind with
  | _ i j =>
    by_cases hij : i = j
    · simpa only [symProd, Sym2.lift_mk, if_pos hij, AddValuation.map_mul,
        WithTop.coe_add] using add_le_add (ha i) (hb i)
    · simp only [symProd, Sym2.lift_mk, if_neg hij]
      exact AddValuation.map_le_add (HahnSeries.addVal ℝ F)
        (by simpa only [AddValuation.map_mul, WithTop.coe_add] using add_le_add (ha i) (hb j))
        (by simpa only [AddValuation.map_mul, WithTop.coe_add] using add_le_add (ha j) (hb i))

theorem quadraticMatrix_entry_nonneg_of_profile {F : Type*} [Field F] {k : ℕ}
    {M : Type*} [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F)
    (w : M → ℝ)
    (hq : ∀ x i, (w x : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (q x i))
    (htri : ∀ x y, dist x y ≤ w x + w y)
    (p : Sym2 (Fin k)) (c : Sym2 M) :
    (0 : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (quadraticMatrix q p c) := by
  induction c using Sym2.ind with
  | _ x y =>
    have hs := symProd_valuation_lower_bound (q x) (q y) (w x) (w y) (hq x) (hq y) p
    have hb : (dist x y : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (symProd (q x) (q y) p) :=
      (WithTop.coe_le_coe.mpr (htri x y)).trans hs
    have hadd := add_le_add_left hb ((-dist x y : ℝ) : WithTop ℝ)
    simpa only [quadraticMatrix, Sym2.lift_mk, AddValuation.map_mul,
      HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero,
      ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero, add_comm] using hadd

theorem minorVal_quadratic_nonneg_of_profile {F : Type*} [Field F] {k : ℕ}
    {M : Type*} [PseudoMetricSpace M] [Fintype M]
    (q : M → Fin k → HahnSeries ℝ F) (w : M → ℝ)
    (hq : ∀ x i, (w x : WithTop ℝ) ≤ HahnSeries.addVal ℝ F (q x i))
    (htri : ∀ x y, dist x y ≤ w x + w y) :
    (0 : WithTop ℝ) ≤ minorVal (quadraticMatrix q) := by
  classical
  rw [minorVal_eq_embeddingMinorVal]
  exact DetValuationMilestone.zero_le_embeddingMinorVal_of_entries
    (HahnSeries.addVal ℝ F) (AddValuation.map_zero _) (AddValuation.map_one _)
    (fun x => AddValuation.map_neg _ x) (fun x y => AddValuation.map_mul _ x y)
    (fun x y => AddValuation.map_add _ x y) (quadraticMatrix q)
    (quadraticMatrix_entry_nonneg_of_profile q w hq htri)

end KServerConj

namespace KServerRepresentation

open KServerConj

theorem initialState_potential_nonneg (k : ℕ) (hk : 1 ≤ k) (N : Type)
    [MetricSpace N] [Fintype N] (p : N) :
    0 ≤ (initialState k hk N p).potential := by
  classical
  let : PseudoMetricSpace (Label k N) := labelSpace k N
  have hq : ∀ (x : Label k N) (i : Fin k),
      (dist p x.1 : WithTop ℝ) ≤
        HahnSeries.addVal ℝ (F k (Label k N)) ((initialState k hk N p).q x i) := by
    intro x i
    change (dist p x.1 : WithTop ℝ) ≤ nu (coef (Sum.inl (i, x)) * zp (dist p x.1))
    simp only [nu_mul, nu_coef, nu_zp, zero_add, le_refl]
  have h := minorVal_quadratic_nonneg_of_profile (initialState k hk N p).q
    (fun x : Label k N => dist p x.1) hq (by
      intro x y
      change dist x.1 y.1 ≤ dist p x.1 + dist p y.1
      simpa only [dist_comm x.1 p] using dist_triangle x.1 p y.1)
  simpa only [(initialState k hk N p).potential_spec, ← WithTop.coe_zero,
    WithTop.coe_le_coe] using h

theorem initialState_potential_eq_zero (k : ℕ) (hk : 1 ≤ k) (N : Type)
    [MetricSpace N] [Fintype N] (p : N) :
    (initialState k hk N p).potential = 0 := by
  apply le_antisymm _ (initialState_potential_nonneg k hk N p)
  simpa only [KServer.workFnU_coalesced_nil k hk N p, dist_self,
    Finset.sum_const_zero, mul_zero] using
    (initialState k hk N p).potential_le_workFnU (fun _ => p)

end KServerRepresentation
end SharpFile066

-- Source: GrowthAccounting.lean
section SharpFile067
open scoped BigOperators

namespace KServerRepresentation

noncomputable def growthSum {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Fin k → N) (σ : List N) (Y : ℕ → Fin k → N) : ℝ :=
  ∑ t ∈ Finset.range σ.length,
    (KServer.workFnU C₀ (σ.take (t + 1)) (Y t) -
      KServer.workFnU C₀ (σ.take t) (Y t))

theorem growthSum_append_singleton {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Fin k → N) (l : List N) (r : N) (Y : ℕ → Fin k → N) :
    growthSum C₀ (l ++ [r]) Y = growthSum C₀ l Y +
      KServer.workFnU C₀ (l ++ [r]) (Y l.length) -
      KServer.workFnU C₀ l (Y l.length) := by
  unfold growthSum
  simp only [List.length_append, List.length_singleton]
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ t ∈ Finset.range l.length,
        (KServer.workFnU C₀ ((l ++ [r]).take (t + 1)) (Y t) -
          KServer.workFnU C₀ ((l ++ [r]).take t) (Y t))) =
      ∑ t ∈ Finset.range l.length,
        (KServer.workFnU C₀ (l.take (t + 1)) (Y t) -
          KServer.workFnU C₀ (l.take t) (Y t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [List.take_append_of_le_length (Nat.succ_le_of_lt (Finset.mem_range.mp ht)),
      List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.mp ht))]
  rw [hsum, List.take_left,
    List.take_of_length_le (by simp only [List.length_append, List.length_singleton, le_refl])]
  exact (add_sub_assoc _ _ _).symm

theorem paid_growth_sum {n : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    (p : N)
    (hinit : (initialState (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p).potential = 0)
    (hstep : ∀ (l : List N) (s : State (n + 2) N p l) (r : N)
      (C : Fin (n + 2) → N),
      ∃ s' : State (n + 2) N p (l ++ [r]),
        KServer.workFnU (fun _ : Fin (n + 2) => p) (l ++ [r]) C -
          KServer.workFnU (fun _ : Fin (n + 2) => p) l C ≤
          s'.potential - s.potential)
    (σ : List N) (Y : ℕ → Fin (n + 2) → N) :
    ∃ s : State (n + 2) N p σ,
      growthSum (fun _ : Fin (n + 2) => p) σ Y ≤ s.potential := by
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨initialState (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p, ?_⟩
    simp only [growthSum, List.length_nil, Finset.range_zero, Finset.sum_empty, hinit,
      le_refl]
  | append_singleton l r ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨s', hs'⟩ := hstep l s r (Y l.length)
    refine ⟨s', ?_⟩
    rw [growthSum_append_singleton]
    linarith only [hs, hs']

end KServerRepresentation
end SharpFile067

-- Source: SharpGrowth.lean
section SharpFile068
namespace KServerRepresentation

theorem exists_paid_state {n : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    (p : N) (σ : List N) (Y : ℕ → Fin (n + 2) → N) :
    ∃ s : State (n + 2) N p σ,
      growthSum (fun _ : Fin (n + 2) => p) σ Y ≤ s.potential := by
  exact paid_growth_sum p
    (initialState_potential_eq_zero (n + 2)
      (Nat.succ_le_succ (Nat.zero_le (n + 1))) N p)
    (fun _ s r C => s.step_potential_growth r C) σ Y

theorem growth_sum_sharp_coalesced {n : ℕ} {N : Type} [MetricSpace N] [Fintype N]
    (p : N) (σ : List N) (Y : ℕ → Fin (n + 2) → N) :
    growthSum (fun _ : Fin (n + 2) => p) σ Y ≤
      (((n + 2 : ℕ) : ℝ) + 1) * KServer.offlineCost (fun _ : Fin (n + 2) => p) σ := by
  obtain ⟨s, hs⟩ := exists_paid_state p σ Y
  exact hs.trans (s.potential_le_offlineCost (Nat.succ_le_succ (Nat.zero_le (n + 1))))

end KServerRepresentation
end SharpFile068

-- Source: Theorems/Thm_KServer_workFnU_antipodal_extension_restrict.lean
section SharpFile070
open KServer

private theorem sharpFile070_mc_nonneg {k : ℕ} {N : Type} [MetricSpace N] (A B : Config k N) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun _ _ => dist_nonneg

private def sharpFile070_Wset {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem sharpFile070_workFn_eq {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) :
    workFn C₀ σ X = sInf (sharpFile070_Wset C₀ σ X) := rfl

private theorem sharpFile070_Wset_bdd {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : BddBelow (sharpFile070_Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => sharpFile070_mc_nonneg _ _
  have h2 := sharpFile070_mc_nonneg (S σ.length) X
  linarith

private theorem sharpFile070_sched_exists {k : ℕ} (hk : 1 ≤ k) {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) : ∃ S : ℕ → Config k N, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private theorem sharpFile070_Wset_nonempty {k : ℕ} (hk : 1 ≤ k) {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : (sharpFile070_Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sharpFile070_sched_exists hk C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem sharpFile070_lab_restrict (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    @workFn k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun i => Sum.inl (X i))
      = workFn C₀ σ X := by
  classical
  let : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set pj : M ⊕ M → M := Sum.elim id id with hpj
  have dproj : ∀ p q : M ⊕ M, dist (pj p) (pj q) ≤ dist p q := by
    rintro (x | x) (y | y)
    · exact le_of_eq rfl
    · show dist x y ≤ 2 * Δ - dist x y
      linarith [hΔ x y]
    · show dist x y ≤ 2 * Δ - dist x y
      linarith [hΔ x y]
    · exact le_of_eq rfl
  have mcl : ∀ A B : Config k M,
      moveCost (fun i => Sum.inl (A i) : Config k (M ⊕ M)) (fun i => Sum.inl (B i))
        = moveCost A B := fun A B => rfl
  have mcp : ∀ P Q : Config k (M ⊕ M),
      moveCost (fun i => pj (P i)) (fun i => pj (Q i)) ≤ moveCost P Q := by
    intro P Q
    exact Finset.sum_le_sum fun i _ => dproj (P i) (Q i)
  have hlen : (σ.map (Sum.inl : M → M ⊕ M)).length = σ.length := by simp
  refine le_antisymm ?_ ?_
  · 
    rw [sharpFile070_workFn_eq, sharpFile070_workFn_eq]
    refine csInf_le_csInf (sharpFile070_Wset_bdd _ _ _) (sharpFile070_Wset_nonempty hk C₀ σ X) ?_
    rintro c ⟨S, hS, rfl⟩
    refine ⟨fun j i => Sum.inl (S j i), ⟨?_, ?_⟩, ?_⟩
    · funext i
      exact congrArg Sum.inl (congrFun hS.1 i)
    · intro j
      have hj' : j.1 < σ.length := by simpa [hlen] using j.2
      obtain ⟨i, hi⟩ := hS.2 ⟨j.1, hj'⟩
      refine ⟨i, ?_⟩
      show Sum.inl (S (↑j + 1) i) = (σ.map Sum.inl).get j
      rw [List.get_eq_getElem, List.getElem_map]
      exact congrArg Sum.inl (by simpa using hi)
    · rw [hlen]
      rw [mcl (S σ.length) X]
      exact congrArg (fun s => s + moveCost (S σ.length) X)
        (Finset.sum_congr rfl fun j _ => (mcl (S j) (S (j + 1))))
  · 
    rw [sharpFile070_workFn_eq, sharpFile070_workFn_eq]
    refine le_csInf (sharpFile070_Wset_nonempty hk _ _ _) ?_
    rintro c ⟨T, hT, rfl⟩
    have hs : ServesFrom C₀ σ (fun j i => pj (T j i)) := by
      constructor
      · funext i
        show pj (T 0 i) = C₀ i
        rw [congrFun hT.1 i]
        rfl
      · intro j
        have hj' : j.1 < (σ.map (Sum.inl : M → M ⊕ M)).length := by simp [hlen]
        obtain ⟨i, hi⟩ := hT.2 ⟨j.1, hj'⟩
        refine ⟨i, ?_⟩
        show pj (T (↑j + 1) i) = σ.get j
        have hi' : T (↑j + 1) i = (σ.map (Sum.inl : M → M ⊕ M)).get ⟨j.1, hj'⟩ := hi
        rw [hi', List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
        rfl
    have hval : (∑ j ∈ Finset.range σ.length,
          moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i)))
        + moveCost (fun i => pj (T σ.length i)) X
        ≤ (∑ j ∈ Finset.range (σ.map (Sum.inl : M → M ⊕ M)).length, moveCost (T j) (T (j + 1)))
          + moveCost (T (σ.map (Sum.inl : M → M ⊕ M)).length) (fun i => Sum.inl (X i)) := by
      
      rw [hlen]
      have h1 : ∀ j, moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i))
          ≤ moveCost (T j) (T (j+1)) := fun j => mcp _ _
      have h2 : moveCost (fun i => pj (T σ.length i)) X ≤ moveCost (T σ.length) (fun i => Sum.inl (X i)) := by
        have := mcp (T σ.length) (fun i => Sum.inl (X i))
        simpa only [hpj, Sum.elim_inl, id_eq] using this
      have hsum : (∑ j ∈ Finset.range σ.length,
            moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i)))
          ≤ ∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1)) :=
        Finset.sum_le_sum fun j _ => h1 j
      linarith [h2, hsum]
    refine le_trans (csInf_le (sharpFile070_Wset_bdd _ _ _) ⟨fun j i => pj (T j i), hs, rfl⟩) hval

theorem KServer.workFnU_antipodal_extension_restrict (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun i => Sum.inl (X i))
      = workFnU C₀ σ X := by
  let : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  unfold workFnU
  refine iInf_congr fun π => ?_
  have h : ((fun i => Sum.inl (X i) : Config k (M ⊕ M)) ∘ π)
      = (fun i => Sum.inl ((X ∘ π) i)) := rfl
  rw [h]
  exact sharpFile070_lab_restrict k hk M Δ hΔ0 hΔ C₀ σ (X ∘ π)
end SharpFile070

-- Exact mission target.
open KServer

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (p : M) (σ : List M) :
    ∑ t ∈ Finset.range σ.length,
        (@workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take (t + 1)).map Sum.inl) (fun _ => Sum.inr (σ.getD t p))
          - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take t).map Sum.inl) (fun _ => Sum.inr (σ.getD t p)))
      ≤ ((k : ℝ) + 1) * offlineCost (fun _ : Fin k => p) σ  := by
  have hk₂ : 2 ≤ k := (show 2 ≤ 3 by decide).trans hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, (Nat.sub_add_cancel hk₂).symm⟩
  let : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  obtain ⟨s, hs⟩ := KServerRepresentation.exists_paid_state (n := n) (Sum.inl p : M ⊕ M)
    (σ.map Sum.inl) (fun t _ => Sum.inr (σ.getD t p))
  have hbound : KServerRepresentation.growthSum
      (fun _ : Fin (n + 2) => (Sum.inl p : M ⊕ M))
      (σ.map Sum.inl) (fun t _ => Sum.inr (σ.getD t p)) ≤
      (((n + 2 : ℕ) : ℝ) + 1) * offlineCost (fun _ : Fin (n + 2) => p) σ := by
    refine le_offlineCost_of_le_workFnU (Nat.succ_le_succ (Nat.zero_le (n + 1)))
      _ _ _ _ (by positivity) ?_
    intro X
    have hb := s.potential_le_workFnU (fun i => Sum.inl (X i))
    rw [workFnU_antipodal_extension_restrict (n + 2)
      (Nat.succ_le_succ (Nat.zero_le (n + 1))) M Δ hΔ0 hΔ (fun _ => p) σ X] at hb
    exact hs.trans hb
  simpa only [KServerRepresentation.growthSum, List.length_map, ← List.map_take] using hbound

#print axioms solution
