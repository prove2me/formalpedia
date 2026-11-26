-- Prove2me | Definitions.Def_ReweightedNPMLE_PolynomialMoments
-- name    : ReweightedNPMLE_PolynomialMoments
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:18:38.202554+00:00
-- url     : https://prove2.me/theorems/0469a52c-a67c-5603-86d7-688e84119f5b
-- title:
--   Monomial feature vectors and Gaussian Taylor polynomials
-- statement:
--   Monomials of total degree at most \(D\) in \(d\) variables are indexed by multisets of length \(D\) drawn from \(d+1\) symbols: one slack symbol has value \(1\), and the other symbols have values \(\theta_1,\ldots,\theta_d\). Their products form the feature vector \(m_{d,D}(\theta)\), with \(\binom{D+d}{d}\) coordinates. A monomial combination is a function \(f(\theta)=\sum_m c_m m_{d,D}(\theta)_m\). Constant, linear, and squared coordinates are specified explicitly; appending multisets multiplies monomials, while padding with slack symbols preserves their values.
--
--   The coordinate dot product and squared norm define \(s(x,\theta)=x\cdot\theta-\|\theta\|^2/2\). The two Taylor polynomials are
--   \[
--   T_L(x,\theta)=\sum_{\ell=0}^L\frac{(x\cdot\theta)^\ell}{\ell!},
--   \qquad
--   P_L(x,\theta)=\sum_{\ell=0}^L\frac{s(x,\theta)^\ell}{\ell!}.
--   \]
--   They have parameter degrees at most \(L\) and \(2L\), respectively. Equivalent evaluation functions are provided for native Euclidean vectors, allowing finite moment vectors to cancel these polynomial terms.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L14-L804

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian

namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype

/--
Coordinates for monomials of total degree at most `D` in `d` variables.

The extra element `0 : Fin (d + 1)` is a homogenizing (slack) variable
whose value is fixed to one.  The remaining elements `Fin.succ i`
represent the `d` genuine variables.
-/
abbrev MonomialCoord (d D : ℕ) := Sym (Fin (d + 1)) D



/-- Evaluate a homogenized variable: the slack variable is `1`. -/
def homogenizedVariable {d : ℕ} (θ : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases 1 θ

/-- Evaluate a monomial coordinate at `θ`. -/
def monomialEval {d D : ℕ} (θ : Fin d → ℝ) (m : MonomialCoord d D) : ℝ :=
  (m.val.map (homogenizedVariable θ)).prod

/-- Vector of all monomials of total degree at most `D`. -/
noncomputable def monomialFeature (d D : ℕ) :
    (Fin d → ℝ) → (MonomialCoord d D → ℝ) :=
  fun θ m ↦ monomialEval θ m









/-- The all-slack coordinate represents the constant monomial `1`. -/
def constantCoord (d D : ℕ) : MonomialCoord d D :=
  Sym.replicate D (0 : Fin (d + 1))

@[simp]
theorem monomialEval_constant (d D : ℕ) (θ : Fin d → ℝ) :
    monomialEval θ (constantCoord d D) = 1 := by
  simp only [monomialEval, constantCoord, Sym.val_replicate]
  simp [homogenizedVariable]

/-- Appending coordinates multiplies their monomial evaluations. -/
@[simp]
theorem monomialEval_append {d D E : ℕ} (θ : Fin d → ℝ)
    (m : MonomialCoord d D) (n : MonomialCoord d E) :
    monomialEval θ (m.append n) = monomialEval θ m * monomialEval θ n := by
  simp [monomialEval, Sym.append, Multiset.map_add]

/-- Pad a monomial with slack variables, without changing its value. -/
def padCoord {d D : ℕ} (E : ℕ) (m : MonomialCoord d D) :
    MonomialCoord d (D + E) :=
  m.append (constantCoord d E)

@[simp]
theorem monomialEval_pad {d D : ℕ} (E : ℕ) (θ : Fin d → ℝ)
    (m : MonomialCoord d D) :
    monomialEval θ (padCoord E m) = monomialEval θ m := by
  simp [padCoord]

/-- A function is a linear combination of the degree-at-most-`D` monomial coordinates. -/
def IsMonomialCombination {d D : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ c : MonomialCoord d D → ℝ,
    ∀ θ, f θ = ∑ m, c m * monomialEval θ m







/-- A sum indexed by any finite type can be collected into monomial coordinates. -/
 theorem isMonomialCombination_reindex {d D : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq (MonomialCoord d D)]
    (c : ι → ℝ) (m : ι → MonomialCoord d D) :
    IsMonomialCombination (d := d) (D := D)
      (fun θ => ∑ i, c i * monomialEval θ (m i)) := by
  classical
  refine ⟨fun q => ∑ i, if m i = q then c i else 0, fun θ => ?_⟩
  simp_rw [sum_mul]
  rw [sum_comm]
  simp



/-- Constant functions are represented by the all-slack coordinate. -/
theorem isMonomialCombination_const {d D : ℕ} (a : ℝ) :
    IsMonomialCombination (d := d) (D := D) (fun _ : Fin d → ℝ => a) := by
  simpa using
    (isMonomialCombination_reindex (d := d) (D := D) (ι := Fin 1)
      (fun _ => a) (fun _ => constantCoord d D))

theorem IsMonomialCombination.add {d D : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := D) g) :
    IsMonomialCombination (d := d) (D := D) (fun θ => f θ + g θ) := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun m => a m + b m, fun θ => ?_⟩
  simp_rw [add_mul, sum_add_distrib, ← ha θ, ← hb θ]

theorem IsMonomialCombination.smul {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) (a : ℝ) :
    IsMonomialCombination (d := d) (D := D) (fun θ => a * f θ) := by
  classical
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun m => a * c m, fun θ => ?_⟩
  change a * f θ = _
  rw [hc θ, mul_sum]
  simp only [mul_assoc]





/-- Finite sums of represented functions remain represented. -/
theorem isMonomialCombination_finsetSum {d D : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, IsMonomialCombination (D := D) (f i)) :
    IsMonomialCombination (d := d) (D := D) (fun θ => ∑ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using isMonomialCombination_const (d := d) (D := D) 0
  | @insert a s ha ih =>
      obtain ⟨c, hc⟩ :=
        (hf a (mem_insert_self a s)).add
          (ih (fun i hi => hf i (mem_insert_of_mem hi)))
      refine ⟨c, fun θ => ?_⟩
      change (∑ i ∈ insert a s, f i θ) = _
      rw [sum_insert ha]
      exact hc θ

/-- Adding slack degree preserves representability. -/
theorem IsMonomialCombination.pad {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) (E : ℕ) :
    IsMonomialCombination (d := d) (D := D + E) f := by
  classical
  obtain ⟨c, hc⟩ := hf
  obtain ⟨a, ha⟩ :=
    isMonomialCombination_reindex (d := d) (D := D + E)
      c (fun m => padCoord E m)
  refine ⟨a, fun θ => ?_⟩
  rw [hc θ]
  simpa using ha θ

/-- Products of represented functions are represented at the sum of the degrees. -/
theorem IsMonomialCombination.mul {d D E : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := E) g) :
    IsMonomialCombination (d := d) (D := D + E) (fun θ => f θ * g θ) := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  obtain ⟨c, hc⟩ :=
    isMonomialCombination_reindex (d := d) (D := D + E)
      (fun p : MonomialCoord d D × MonomialCoord d E => a p.1 * b p.2)
      (fun p => p.1.append p.2)
  refine ⟨c, fun θ => ?_⟩
  change f θ * g θ = _
  rw [ha θ, hb θ, sum_mul]
  simp_rw [mul_sum]
  rw [← Fintype.sum_prod_type']
  calc
    (∑ p : MonomialCoord d D × MonomialCoord d E,
        (a p.1 * monomialEval θ p.1) * (b p.2 * monomialEval θ p.2)) =
        ∑ p : MonomialCoord d D × MonomialCoord d E,
          (a p.1 * b p.2) * monomialEval θ (p.1.append p.2) := by
            refine Fintype.sum_congr _ _ fun p => ?_
            simp only [monomialEval_append]
            ring
    _ = ∑ q, c q * monomialEval θ q := hc θ

/-- Degree-one coordinate for the genuine variable `θ i`. -/
def linearCoordOne {d : ℕ} (i : Fin d) : MonomialCoord d 1 :=
  Fin.succ i ::ₛ Sym.nil

@[simp]
theorem monomialEval_linearOne {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (linearCoordOne i) = θ i := by
  simp only [monomialEval, linearCoordOne, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable]

/-- Degree-two coordinate for the linear monomial `θ i` (one slack factor). -/
def linearCoord {d : ℕ} (i : Fin d) : MonomialCoord d 2 :=
  (0 : Fin (d + 1)) ::ₛ Fin.succ i ::ₛ Sym.nil

/-- Degree-two coordinate for the quadratic monomial `(θ i)^2`. -/
def squareCoord {d : ℕ} (i : Fin d) : MonomialCoord d 2 :=
  Fin.succ i ::ₛ Fin.succ i ::ₛ Sym.nil





/-- The Euclidean dot product, written explicitly in finite coordinates. -/
def coordinateDot {d : ℕ} (x θ : Fin d → ℝ) : ℝ :=
  ∑ i, x i * θ i



/-- A coordinate dot product is a polynomial of total degree at most one. -/
theorem coordinateDot_isMonomialCombination_one {d : ℕ} (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 1) (coordinateDot x) := by
  simpa [coordinateDot] using
    (isMonomialCombination_reindex (d := d) (D := 1)
      x (fun i ↦ linearCoordOne i))

/-- The `ell`th power of a dot product has degree at most `ell`. -/
theorem coordinateDot_pow_isMonomialCombination {d : ℕ}
    (x : Fin d → ℝ) (ell : ℕ) :
    IsMonomialCombination (d := d) (D := ell)
      (fun θ ↦ (coordinateDot x θ) ^ ell) := by
  induction ell with
  | zero => simpa using isMonomialCombination_const (d := d) (D := 0) 1
  | succ ell ih =>
      simpa [pow_succ] using ih.mul (coordinateDot_isMonomialCombination_one x)

/-- The exponential series in a dot product, truncated after order `L`. -/
noncomputable def coordinateTruncatedInnerExp {d : ℕ} (L : ℕ)
    (x θ : Fin d → ℝ) : ℝ :=
  ∑ ell ∈ range (L + 1), (coordinateDot x θ) ^ ell / ell.factorial

/-- Taylor polynomial for `exp ⟪θ,η⟫`, expressed on the native Euclidean
parameter space. -/
noncomputable def pointTruncatedInnerExp {d : ℕ} (L : ℕ)
    (θ η : Point d) : ℝ :=
  ∑ ell ∈ range (L + 1), (inner ℝ θ η) ^ ell / ell.factorial

/-- The truncated inner-product exponential has degree at most `L`. -/
theorem coordinateTruncatedInnerExp_isMonomialCombination {d : ℕ}
    (L : ℕ) (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := L)
      (coordinateTruncatedInnerExp L x) := by
  have hterm : ∀ ell ∈ range (L + 1),
      IsMonomialCombination (d := d) (D := L)
        (fun θ ↦ (coordinateDot x θ) ^ ell / ell.factorial) := by
    intro ell hell
    have hell_le : ell ≤ L := Nat.le_of_lt_succ (mem_range.mp hell)
    have hpadded := (coordinateDot_pow_isMonomialCombination x ell).pad (L - ell)
    have hdegree : ell + (L - ell) = L := Nat.add_sub_of_le hell_le
    rw [hdegree] at hpadded
    simpa [div_eq_mul_inv, mul_comm] using
      hpadded.smul ((ell.factorial : ℝ)⁻¹)
  exact isMonomialCombination_finsetSum (range (L + 1))
    (fun ell θ ↦ (coordinateDot x θ) ^ ell / ell.factorial) hterm



/-- The squared Euclidean norm, written explicitly in finite coordinates. -/
def coordinateNormSq {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i, (θ i) ^ 2

/-- The Gaussian score `x · θ - ‖θ‖² / 2`. -/
noncomputable def coordinateGaussianScore {d : ℕ} (x θ : Fin d → ℝ) : ℝ :=
  coordinateDot x θ - (1 / 2 : ℝ) * coordinateNormSq θ







/-- The exponential series in the Gaussian score, truncated after order `L`. -/
noncomputable def coordinateGaussianTruncatedScoreExp {d : ℕ} (L : ℕ)
    (x θ : Fin d → ℝ) : ℝ :=
  ∑ ell ∈ range (L + 1), (coordinateGaussianScore x θ) ^ ell / ell.factorial















/-- Monomial evaluation on the Euclidean-space representation used by the NPMLE theorem. -/
def pointMonomialEval {d D : ℕ}
    (θ : Point d) (m : MonomialCoord d D) : ℝ :=
  monomialEval (fun i ↦ θ i) m



/-- The inner-product exponential Taylor polynomial uses exactly the
degree-at-most-`L` monomial coordinates appearing in Proposition 4.1. -/
theorem truncatedInnerExp_isPointMonomialCombination
    {d : ℕ} (L : ℕ) (x : Point d) :
    ∃ c : MonomialCoord d L → ℝ,
      ∀ θ : Point d,
        (∑ ell ∈ range (L + 1),
          (inner ℝ x θ) ^ ell / ell.factorial) =
            ∑ m, c m * pointMonomialEval θ m := by
  obtain ⟨c, hc⟩ :=
    coordinateTruncatedInnerExp_isMonomialCombination L (fun i ↦ x i)
  refine ⟨c, fun θ ↦ ?_⟩
  have hinner : inner ℝ x θ = coordinateDot (fun i ↦ x i) (fun i ↦ θ i) := by
    rw [coordinateDot, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [coordinateTruncatedInnerExp] at hc
  rw [hinner]
  exact hc (fun i ↦ θ i)









end ReweightedNPMLE


