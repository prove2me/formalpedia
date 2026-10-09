-- Prove2me | Definitions.Def_Nonadditivity_SpectralDamping
-- name    : Nonadditivity_SpectralDamping
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:46:47.151973+00:00
-- url     : https://prove2.me/theorems/1f5340b2-3838-4c82-a1cc-e795e668153c
-- title:
--   Simultaneous spectral damping with a controlled trace cost
-- statement:
--   On a finite nonempty matrix index set, for a Hermitian matrix $A=U\operatorname{diag}(\lambda_i)U^*$ and a real function $f$, define $f(A)=U\operatorname{diag}(f(\lambda_i))U^*$. This spectral calculus preserves sums, products, powers, order, and trace. Given a finite family of Hermitian matrices $(X_q)_{q\in Q}$, a scale $L>0$, and an integer $p\ge1$, form
--   $$R=\sum_{q\in Q}(L^{-1}X_q)^{2p},\qquad F=(I+R)^{-1},\qquad G=I+R.$$
--   The bundle proves $F=F^*$, $I-F^2\succeq0$, $GF=I$, and
--   $$\|FX_qF\|\le L\quad(q\in Q),\qquad\operatorname{Re}\operatorname{Tr}(I-F^2)\le2\sum_{q\in Q}L^{-2p}\operatorname{Re}\operatorname{Tr}(X_q^{2p}).$$
--   Thus one invertible filter suppresses the entire family while its discarded trace is explicitly bounded by the prescribed even moments. The supporting order inequalities and functional-calculus identities are proved inside the bundle.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/SpectralDamping.lean#L20-L312

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Star.Unitary

namespace Nonadditivity.GaussianNormalization
end Nonadditivity.GaussianNormalization

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! Finite moment damping: an actual positive contraction simultaneously suppresses
all operators in a finite family, at a trace cost controlled by their even moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.SpectralDamping
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {D Q : Type*} [Fintype D] [DecidableEq D] [Nonempty D] [Fintype Q]

/-- Functional calculus in a fixed Hermitian eigenbasis. -/
def spectral (A : Matrix D D ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix D D ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal fun i => (f (hA.eigenvalues i) : ℂ))

theorem spectral_id (A : Matrix D D ℂ) (hA : A.IsHermitian) :
    spectral A hA id = A := hA.spectral_theorem.symm

theorem spectral_one (A : Matrix D D ℂ) (hA : A.IsHermitian) :
    spectral A hA (fun _ => 1) = 1 := by simp [spectral]

theorem spectral_add (A : Matrix D D ℂ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectral A hA (fun x => f x + g x) = spectral A hA f + spectral A hA g := by
  unfold spectral
  rw [←map_add]
  congr 1
  ext i j
  by_cases h:i=j <;> simp [h]

theorem spectral_sub (A : Matrix D D ℂ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectral A hA (fun x => f x - g x) = spectral A hA f - spectral A hA g := by
  unfold spectral
  rw [←map_sub]
  congr 1
  ext i j
  by_cases h:i=j <;> simp [h]

theorem spectral_mul (A : Matrix D D ℂ) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectral A hA (fun x => f x * g x) = spectral A hA f * spectral A hA g := by
  simp only [spectral,Complex.ofReal_mul,←Matrix.diagonal_mul_diagonal,map_mul]

theorem spectral_pow (A : Matrix D D ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) (p : ℕ) :
    spectral A hA (fun x => f x ^ p) = spectral A hA f ^ p := by
  unfold spectral
  rw [←map_pow,Matrix.diagonal_pow]
  congr 1
  ext i j
  by_cases h:i=j <;> simp [h,Pi.pow_apply]

theorem spectral_smul (A : Matrix D D ℂ) (hA : A.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    spectral A hA (fun x => c * f x) = c • spectral A hA f := by
  simp only [spectral,Complex.ofReal_mul]
  rw [show (Matrix.diagonal fun i => (c:ℂ)*(f (hA.eigenvalues i):ℂ)) =
    (c:ℂ) • Matrix.diagonal (fun i => (f (hA.eigenvalues i):ℂ)) by
      ext i j; by_cases h:i=j <;> simp [h]]
  rw [map_smul]
  rfl

theorem spectral_posSemidef (A : Matrix D D ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (spectral A hA f).PosSemidef := by
  apply Matrix.LE.le.posSemidef
  unfold spectral
  exact map_nonneg (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary)
    (Matrix.PosSemidef.nonneg (Matrix.posSemidef_diagonal_iff.mpr (fun i => by
      exact_mod_cast hf i)))

theorem spectral_hermitian (A : Matrix D D ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (spectral A hA f).IsHermitian := by
  change star (spectral A hA f) = spectral A hA f
  unfold spectral
  rw [←map_star]
  congr 1
  ext i j
  by_cases h:i=j
  · subst j; simp [Matrix.star_apply]
  · simp [Matrix.star_apply,h,Ne.symm h]

theorem spectral_mono (A : Matrix D D ℂ) (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ i, f (hA.eigenvalues i) ≤ g (hA.eigenvalues i)) :
    spectral A hA f ≤ spectral A hA g := by
  rw [Matrix.le_iff,←spectral_sub]
  exact spectral_posSemidef A hA _ (fun i => sub_nonneg.mpr (hfg i))

theorem spectral_trace (A : Matrix D D ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (spectral A hA f).trace.re = ∑ i, f (hA.eigenvalues i) := by
  simp only [spectral,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self,Matrix.one_mul,Matrix.trace_diagonal]
  simp

/-- The damping matrix is precisely `(I+R)⁻¹` in a Hermitian eigenbasis. -/
def damping (R : Matrix D D ℂ) (hR : R.IsHermitian) : Matrix D D ℂ :=
  spectral R hR (fun r => (1+r)⁻¹)

theorem damping_hermitian (R : Matrix D D ℂ) (hR : R.IsHermitian) :
    (damping R hR).IsHermitian := spectral_hermitian _ _ _



theorem damping_le_one (R : Matrix D D ℂ) (hR : R.PosSemidef) :
    damping R hR.isHermitian ≤ 1 := by
  rw [←spectral_one R hR.isHermitian]
  exact spectral_mono _ _ _ _ (fun i => inv_le_one_of_one_le₀ (by
    have := hR.eigenvalues_nonneg i; linarith))



theorem damping_residual_posSemidef (R : Matrix D D ℂ) (hR : R.PosSemidef) :
    (1-damping R hR.isHermitian*damping R hR.isHermitian).PosSemidef := by
  rw [damping,←spectral_mul,←spectral_one R hR.isHermitian,←spectral_sub]
  apply spectral_posSemidef
  intro i
  have h0 : 0 ≤ (1+hR.isHermitian.eigenvalues i)⁻¹ := by
    have := hR.eigenvalues_nonneg i; positivity
  have h1 : (1+hR.isHermitian.eigenvalues i)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by have := hR.eigenvalues_nonneg i; linarith)
  nlinarith

theorem damping_identity (R : Matrix D D ℂ) (hR : R.PosSemidef) :
    damping R hR.isHermitian * (1+R) * damping R hR.isHermitian =
      damping R hR.isHermitian := by
  have he : 1+R = spectral R hR.isHermitian (fun r => 1+r) := by
    rw [spectral_add,spectral_one]; exact congrArg (1+·) (spectral_id R hR.isHermitian).symm
  rw [he,damping,←spectral_mul,←spectral_mul]
  unfold spectral
  congr 2
  funext i
  have hn : 1+hR.isHermitian.eigenvalues i ≠ 0 := by
    have := hR.eigenvalues_nonneg i; linarith
  simp [hn]

/-- The actual normalized loss of trace tends to zero when the normalized penalty does. -/
theorem damping_trace_loss (R : Matrix D D ℂ) (hR : R.PosSemidef) :
    (1-damping R hR.isHermitian*damping R hR.isHermitian).trace.re ≤ 2*R.trace.re := by
  rw [damping,←spectral_mul,←spectral_one R hR.isHermitian,←spectral_sub,spectral_trace,
    show R.trace.re = ∑ i, hR.isHermitian.eigenvalues i from by
      simpa using HaarMomentTail.trace_pow_re_eq_sum R hR.isHermitian 1,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hr := hR.eigenvalues_nonneg i
  have hp : 0 < 1+hR.isHermitian.eigenvalues i := by linarith
  have hid : (1+hR.isHermitian.eigenvalues i) * (1+hR.isHermitian.eigenvalues i)⁻¹ = 1 :=
    mul_inv_cancel₀ hp.ne'
  have hinv : 0 ≤ (1+hR.isHermitian.eigenvalues i)⁻¹ := inv_nonneg.mpr hp.le
  have hs : 0 ≤ hR.isHermitian.eigenvalues i * (1+hR.isHermitian.eigenvalues i)⁻¹ :=
    mul_nonneg hr hinv
  nlinarith [sq_nonneg (hR.isHermitian.eigenvalues i * (1+hR.isHermitian.eigenvalues i)⁻¹)]

/-- Hermitian order bounds give the actual Euclidean operator-norm bound. -/
theorem norm_le_of_bounds (A : Matrix D D ℂ) (hA : A.IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hl : (-L) • (1 : Matrix D D ℂ) ≤ A)
    (hu : A ≤ L • (1 : Matrix D D ℂ)) : ‖A‖ ≤ L := by
  letI : CStarAlgebra (Matrix D D ℂ) := {}
  have hupper : ∀ x ∈ spectrum ℝ A, x ≤ L :=
    (le_algebraMap_iff_spectrum_le hA).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hu)
  have hlower : ∀ x ∈ spectrum ℝ A, -L ≤ x :=
    (algebraMap_le_iff_le_spectrum hA).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hl)
  have he (i : D) : hA.eigenvalues i ∈ spectrum ℝ A := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i,rfl⟩
  conv_lhs => rw [hA.spectral_theorem]
  rw [StarAlgEquiv.norm_map,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hL).mpr
  intro i
  change ‖(hA.eigenvalues i : ℂ)‖ ≤ L
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    (abs_le.mpr ⟨hlower _ (he i),hupper _ (he i)⟩)

theorem congruence_mono (F : Matrix D D ℂ) (hF : F.IsHermitian)
    {A B : Matrix D D ℂ} (hAB : A ≤ B) : F*A*F ≤ F*B*F := by
  rw [Matrix.le_iff] at hAB ⊢
  simpa only [hF.eq,Matrix.mul_sub,Matrix.sub_mul] using
    hAB.conjTranspose_mul_mul_same F

theorem damping_sandwich_norm_le (R : Matrix D D ℂ) (hR : R.PosSemidef)
    (X : Matrix D D ℂ) (hX : X.IsHermitian)
    (hl : -(1+R) ≤ X) (hu : X ≤ 1+R) :
    ‖damping R hR.isHermitian * X * damping R hR.isHermitian‖ ≤ 1 := by
  let F := damping R hR.isHermitian
  have hF : F.IsHermitian := damping_hermitian _ _
  have hu' : F*X*F ≤ F := by
    have h := congruence_mono F hF hu
    simpa only [F,damping_identity R hR] using h
  have hl' : -F ≤ F*X*F := by
    have h := congruence_mono F hF hl
    simpa only [F,Matrix.mul_neg,Matrix.neg_mul,damping_identity R hR] using h
  have hf1 : F ≤ 1 := damping_le_one R hR
  apply norm_le_of_bounds _ (by
    simpa only [hF.eq] using Matrix.isHermitian_conjTranspose_mul_mul F hX) zero_le_one
  · simpa only [neg_smul,one_smul] using (neg_le_neg hf1).trans hl'
  · simpa only [one_smul] using hu'.trans hf1

theorem abs_le_one_add_even_pow (x : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    |x| ≤ 1+x^(2*p) := by
  have hn : 0 ≤ x^(2*p) := by rw [pow_mul]; positivity
  by_cases hx : |x| ≤ 1
  · linarith
  · have hpow := le_self_pow₀ (le_of_not_ge hx) (show 2*p≠0 by omega)
    have habs : |x|^(2*p) = x^(2*p) := by simp only [pow_mul,sq_abs]
    rw [habs] at hpow
    linarith

theorem even_power_posSemidef (X : Matrix D D ℂ) (hX : X.IsHermitian) (p : ℕ) :
    (X^(2*p)).PosSemidef := by
  have h := spectral_posSemidef X hX (fun x => x^(2*p)) (fun i => by dsimp; rw [pow_mul]; positivity)
  rw [spectral_pow] at h
  change (spectral X hX id ^ (2*p)).PosSemidef at h
  rwa [spectral_id] at h

theorem even_power_bounds (X : Matrix D D ℂ) (hX : X.IsHermitian)
    (p : ℕ) (hp : 1 ≤ p) : -(1+X^(2*p)) ≤ X ∧ X ≤ 1+X^(2*p) := by
  have hu := spectral_mono X hX id (fun x => 1+x^(2*p)) (fun i =>
    (le_abs_self _).trans (abs_le_one_add_even_pow _ p hp))
  have hl := spectral_mono X hX (fun x => -(1+x^(2*p))) id (fun i => by
    have h := abs_le_one_add_even_pow (hX.eigenvalues i) p hp
    have h' := neg_abs_le (hX.eigenvalues i)
    dsimp only [id_eq]
    linarith)
  have hn : spectral X hX (fun x => -(1+x^(2*p))) =
      -(spectral X hX (fun x => 1+x^(2*p))) := by
    simpa using spectral_smul X hX (-1) (fun x => 1+x^(2*p))
  have he : spectral X hX (fun x => 1+x^(2*p)) = 1+X^(2*p) := by
    rw [spectral_add,spectral_one,spectral_pow]
    change 1+spectral X hX id^(2*p) = _
    rw [spectral_id]
  rw [hn,he,spectral_id] at hl
  rw [he,spectral_id] at hu
  exact ⟨hl,hu⟩

/-- The finite penalty uses only the requested fixed even moment. -/
def penalty (X : Q → Matrix D D ℂ) (p : ℕ) : Matrix D D ℂ := ∑ q, X q^(2*p)

theorem penalty_posSemidef (X : Q → Matrix D D ℂ) (hX : ∀ q, (X q).IsHermitian)
    (p : ℕ) : (penalty X p).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ (fun q _ => even_power_posSemidef (X q) (hX q) p)

theorem penalty_bounds (X : Q → Matrix D D ℂ) (hX : ∀ q, (X q).IsHermitian)
    (p : ℕ) (hp : 1 ≤ p) (q : Q) :
    -(1+penalty X p) ≤ X q ∧ X q ≤ 1+penalty X p := by
  have hsum : X q^(2*p) ≤ penalty X p := Finset.single_le_sum
    (fun i _ => (even_power_posSemidef (X i) (hX i) p).nonneg) (Finset.mem_univ q)
  have hb := even_power_bounds (X q) (hX q) p hp
  exact ⟨(neg_le_neg (add_le_add (le_refl (1 : Matrix D D ℂ)) hsum)).trans hb.1,
    hb.2.trans (add_le_add (le_refl (1 : Matrix D D ℂ)) hsum)⟩

/-- A single explicitly constructed contraction suppresses every member of the family. -/
theorem family_damping_norm_le (X : Q → Matrix D D ℂ)
    (hX : ∀ q, (X q).IsHermitian) (p : ℕ) (hp : 1 ≤ p) (q : Q) :
    ‖damping (penalty X p) (penalty_posSemidef X hX p).isHermitian * X q *
      damping (penalty X p) (penalty_posSemidef X hX p).isHermitian‖ ≤ 1 :=
  damping_sandwich_norm_le _ (penalty_posSemidef X hX p) _ (hX q)
    (penalty_bounds X hX p hp q).1 (penalty_bounds X hX p hp q).2

theorem penalty_trace (X : Q → Matrix D D ℂ) (p : ℕ) :
    (penalty X p).trace.re = ∑ q, (X q^(2*p)).trace.re := by
  simp [penalty,Matrix.trace_sum]

theorem damping_left_inverse (R : Matrix D D ℂ) (hR : R.PosSemidef) :
    (1+R)*damping R hR.isHermitian = 1 := by
  have he : 1+R = spectral R hR.isHermitian (fun r => 1+r) := by
    rw [spectral_add,spectral_one]
    exact congrArg (1+·) (spectral_id R hR.isHermitian).symm
  rw [he,damping,←spectral_mul,←spectral_one R hR.isHermitian]
  unfold spectral
  congr 2
  funext i
  have hn : 1+hR.isHermitian.eigenvalues i ≠ 0 := by
    have := hR.eigenvalues_nonneg i; linarith
  simp [hn]

/-- Fixed moments yield an actual simultaneously damped family, with its exact trace cost
and an explicit left inverse. No convergence or random-matrix estimate is assumed. -/
theorem exists_damping (X : Q → Matrix D D ℂ) (hX : ∀ q, (X q).IsHermitian)
    (L : ℝ) (hL : 0 < L) (p : ℕ) (hp : 1 ≤ p) :
    ∃ F G : Matrix D D ℂ, F.IsHermitian ∧ (1-F*F).PosSemidef ∧ G*F=1 ∧
      (∀ q, ‖F*X q*F‖ ≤ L) ∧
      (1-F*F).trace.re ≤ 2 * ∑ q, (L⁻¹)^(2*p) * (X q^(2*p)).trace.re := by
  let Y : Q → Matrix D D ℂ := fun q => (L⁻¹ : ℝ) • X q
  have hY (q : Q) : (Y q).IsHermitian := by
    change star ((L⁻¹ : ℝ) • X q) = (L⁻¹ : ℝ) • X q
    simp only [star_smul,star_trivial]
    change (L⁻¹ : ℝ) • (X q).conjTranspose = (L⁻¹ : ℝ) • X q
    rw [(hX q).eq]
  let R := penalty Y p
  have hR : R.PosSemidef := penalty_posSemidef Y hY p
  let F := damping R hR.isHermitian
  refine ⟨F,1+R,damping_hermitian _ _,damping_residual_posSemidef _ hR,
    damping_left_inverse _ hR,?_,?_⟩
  · intro q
    have hb : ‖F*Y q*F‖ ≤ 1 := family_damping_norm_le Y hY p hp q
    have he : F*X q*F = L • (F*Y q*F) := by
      simp only [Y,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_inv_cancel₀ hL.ne',one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hL]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hL.le
  · have hb := damping_trace_loss R hR
    simpa only [R,penalty_trace,Y,smul_pow,Matrix.trace_smul,Complex.smul_re,smul_eq_mul] using hb

end Nonadditivity.SpectralDamping


