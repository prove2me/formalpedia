-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
-- name    : ErdosProblems_Erdos1041_Counterexample_InstanceCritical
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T19:00:22.973858+00:00
-- url     : https://prove2.me/theorems/62c19b7b-000e-45e6-bd53-e6b85149336a
-- title:
--   Exact root and critical-point certificate data
-- statement:
--   Defines rational brackets, root selectors, rescaled radii, and auxiliary certificate polynomials for the fixed degree-seven instance. The module’s later theorems prove the required uniqueness, location, and numerical margins.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L1-L4310
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of the concrete critical configuration of `ani_degree7_counterexample.tex`
at `s = 10^-6`. -/

/-
Slice S4.  Helper development lives in `Erdos1041.Counterexample.S4Proofs`; the
obligations are re-exported at the interface names
`Erdos1041.Counterexample.s4_f_monic_degree`, `s4_roots_on_circle`,
`s4_roots_nodup` at the end of the file.

The root argument follows a Cayley-transform route.  With
`chi x = (1 + i x)/(1 - i x)` one has the
exact Gaussian-rational identity `(1 - i x)^7 F(chi x) = 2 i H(x)` for an
explicit degree-seven *real* polynomial `H`, and seven exact rational sign
changes of `H` produce seven distinct roots of `F` of modulus exactly one.
-/

noncomputable section
open scoped ComplexConjugate NNReal
namespace Erdos1041.Counterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## §A  Trigonometric anchors for the seventh roots of unity

Public, because slices S5 and S7 need the same enclosures.  Everything is
derived from one Chebyshev relation, `8c³ + 4c² − 4c − 1 = 0` for
`c = cos(2π/7)`, together with `Real.pi_gt_d6` / `Real.pi_lt_d6`.  This is the
only place in slice S4 where `Real.pi` enters; every other estimate is exact
rational arithmetic. -/

















/-! ### The seventh roots of unity as powers of `u 1` -/

















/-! ### Rational enclosures of `Re u j`, `Im u j` for `j = 0,…,6`

Obtained by six steps of interval multiplication from `u 1`; the widest box is
`j = 6`, at `6·10⁻³`.  Every row is verified against
`INSTANCE_CERTIFICATES.md` §1. -/















/-! ### The two anchors named in the interface statement -/





/-! ### Separation of the seven anchors

`‖u i - u j‖ ≥ 2 sin(π/7) > 0.867` for `i ≠ j`; only the crude bound `1/5` is
needed, and only against `u 3` and `u 6`. -/







namespace S4Proofs

/-! ## Basic facts about the constants -/











/-! ## The first obligation: `f` is monic of degree seven -/



/-! ## Exact scaling identities -/





theorem conj_a : conj a = (A : ℂ) + (s : ℂ) * Complex.I := by
  simp only [a, map_sub, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_b : conj b = -(Complex.I * (B : ℂ)) + ((9 / 5 : ℚ) : ℂ) * (s : ℂ) := by
  simp only [b, map_add, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_c : conj c = -(Cconst : ℂ) + ((162 / 25 : ℚ) : ℂ) * (s : ℂ) * Complex.I := by
  simp only [c, map_sub, map_neg, map_mul, map_ratCast, Complex.conj_I]
  ring







/-! ## A Cayley-transform replacement for the nested root disks

Write `chi x = (1 + i x)/(1 - i x)`.  The real polynomial `H` below satisfies
`(1 - i x)^7 F(chi x) = 2 i H(x)`.  Seven rational sign changes give seven
distinct unit-modulus roots directly.  This avoids a root-counting contour
theorem and avoids approximate-to-exact reflection arguments.
-/

def cayley (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * Complex.I) / (1 - (x : ℂ) * Complex.I)

def cayleyH (x : ℝ) : ℝ :=
    7 * x - 35 * x ^ 3 + 21 * x ^ 5 - x ^ 7
      - (ε : ℝ) ^ 4 * (1 + x ^ 2) ^ 3 * ((s : ℝ) + (A : ℝ) * x)
      + (ε : ℝ) ^ 5 * (1 + x ^ 2) ^ 2 *
          ((B : ℝ) * (1 - 3 * x ^ 2) + (9 / 5 : ℝ) * (s : ℝ) * (x ^ 3 - 3 * x))
      + (ε : ℝ) ^ 6 * (1 + x ^ 2) *
          ((Cconst : ℝ) * (5 * x - 10 * x ^ 3 + x ^ 5)
            - (162 / 25 : ℝ) * (s : ℝ) * (1 - 10 * x ^ 2 + 5 * x ^ 4))

def bracketLo : Fin 7 → ℝ :=
  ![-1 / 10000, 4815 / 10000, 12539 / 10000, 43812 / 10000,
    -43813 / 10000, -12540 / 10000, -4816 / 10000]

def bracketHi : Fin 7 → ℝ :=
  ![1 / 10000, 4816 / 10000, 12540 / 10000, 43813 / 10000,
    -43812 / 10000, -12539 / 10000, -4815 / 10000]









theorem cayleyH_continuous : Continuous cayleyH := by
  unfold cayleyH
  fun_prop

/-- Seven exact sign changes, not floating-point approximations. -/
theorem cayley_signs (j : Fin 7) :
    bracketLo j < bracketHi j ∧
      ((cayleyH (bracketLo j) < 0 ∧ 0 < cayleyH (bracketHi j)) ∨
       (cayleyH (bracketHi j) < 0 ∧ 0 < cayleyH (bracketLo j))) := by
  fin_cases j <;>
    norm_num [bracketLo, bracketHi, cayleyH, ε, s, A, B, Cconst, t]

theorem exists_cayley_root (j : Fin 7) :
    ∃ x : ℝ, x ∈ Set.Ioo (bracketLo j) (bracketHi j) ∧ cayleyH x = 0 := by
  rcases cayley_signs j with ⟨hab, hs⟩
  rcases hs with hs | hs
  · exact intermediate_value_Ioo hab.le cayleyH_continuous.continuousOn hs
  · exact intermediate_value_Ioo' hab.le cayleyH_continuous.continuousOn hs

def realRoot (j : Fin 7) : ℝ := Classical.choose (exists_cayley_root j)







/-- The seven physical roots constructed from the seven real brackets. -/
def physicalRoot (j : Fin 7) : ℂ := (ρ : ℂ) * cayley (realRoot j)









/-- The seven roots as a multiset (no `DecidableEq ℂ` needed). -/
def rootMul : Multiset ℂ := Multiset.map physicalRoot Finset.univ.val

















/-! ## The constructed roots sit next to the seventh roots of unity

`cayley x - w = ((1 + ix) - w(1 - ix)) / (1 - ix)`, so the whole estimate is a
rational computation in `x`, `Re w`, `Im w` with no division and no
trigonometry beyond the anchor enclosures of §A.  The uniform deviation budget
`1/100` covers every one of the seven cases (worst case `8·10⁻³`, at `j = 4`). -/





















/-! ## The `shiftQuad` bridge

`shiftQuad p cc` is defined by division by the monic `X ^ 2`.  At a critical
point the constant and linear coefficients of `p.comp (X + C cc) - C (p.eval cc)`
both vanish, so the division is exact and the defining identity holds. -/



/-! ## Transport of the critical points from `Q` to `f`

`f'(ρεw) = ρ⁶ε⁶ Q'(w)` (paper (4.4)), so `w ↦ ρεw` is a bijection carrying the
zeros of `Q'` onto the zeros of `f'`, degree for degree. -/

theorem derivative_Q_eval (w : ℂ) :
    (Polynomial.derivative Q).eval w
      = 7 * w ^ 6 + 3 * a * w ^ 2 + 2 * b * w + c
        - 4 * (s : ℂ) ^ 2 * conj a * w ^ 3
        - 5 * (s : ℂ) ^ 6 * conj b * w ^ 4
        - 6 * (s : ℂ) ^ 10 * conj c * w ^ 5 := by
  simp only [Q, P, G, E, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero, a, b, c]
  push_cast
  ring







/-! ## A Newton contraction bridge for the critical-point localisation -/

/-- A Newton map on a nonempty complete set gives a unique zero.

For the S4 critical disks, use `p z = (Polynomial.derivative Q).eval z` and
`d = (Polynomial.derivative (Polynomial.derivative Q)).eval centre`.  Finite
Taylor inequalities provide `hmap` and `hlip`. -/
theorem exists_unique_zero_of_newton_contraction
    (p : ℂ → ℂ) (S : Set ℂ) (hcomplete : IsComplete S)
    (x₀ : ℂ) (hx₀ : x₀ ∈ S) (d : ℂ) (hd : d ≠ 0)
    (hmap : ∀ z ∈ S, z - p z / d ∈ S)
    (hlip : ∀ x ∈ S, ∀ y ∈ S,
      ‖(x - p x / d) - (y - p y / d)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖) :
    ∃! z : ℂ, z ∈ S ∧ p z = 0 := by
  let step : ℂ → ℂ := fun z => z - p z / d
  have hmaps : Set.MapsTo step S S := hmap
  have hc : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict step S S) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have := hlip x.val x.property y.val y.property
      simpa [step, Set.MapsTo.restrict, Subtype.dist_eq, dist_eq_norm] using this
  obtain ⟨z, hz, hfixed, _, _⟩ :=
    hc.exists_fixedPoint' hcomplete hmaps hx₀ (edist_ne_top _ _)
  have hzroot : p z = 0 := by
    have hf : z - p z / d = z := hfixed
    have hdiv : p z / d = 0 := by linear_combination -hf
    exact (div_eq_zero_iff.mp hdiv).resolve_right hd
  refine ⟨z, ⟨hz, hzroot⟩, ?_⟩
  intro w hw
  have hdist := hlip w hw.1 z hz
  simp only [hw.2, hzroot, zero_div, sub_zero] at hdist
  have hn : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-! ## Exact arithmetic budgets for the critical package

These are the rational margin checks of `INSTANCE_CERTIFICATES.md`, restated as
exact rational inequalities. -/













/-! ## The lemniscate defect `H_s` in the scaled coordinate -/

/-- `K₀ = (ρ⁻¹⁴ - 1)/(2ε⁷)` (paper (4.5)), written without a reciprocal. -/
def K0 : ℝ := (1 - (ρ : ℝ) ^ 14) / (2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7)

/-- `H_s(w) = K₀ + Re Q_s(w) - (ε⁷/2)|Q_s(w)|²` (paper (4.6)). -/
def Hs (w : ℂ) : ℝ :=
  K0 + (Q.eval w).re - ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w)








end S4Proofs

/-! ## Root-localisation conjuncts of `s4_instance_critical`

Public: S7 consumes these directly.  The witnesses are
`b₃ = S4Proofs.physicalRoot 3` and `b₆ = S4Proofs.physicalRoot 6`. -/



















/-! ## The S4 obligations at their interface names -/







end Erdos1041.Counterexample

-- BEGIN GENERATED: coarse instance certificates
-- Regenerate with
--   ./repo-python formal_math/erdos1041_external_counterexample/emit_instance_certificates.py
-- Numbers verified exactly by instance_certificates_coarse.py (26/26 checks).

namespace Erdos1041.Counterexample.S4Proofs

/-! ### The constants as rational-cast Gaussian rationals

Every constant is kept in the shape `((x : ℚ) : ℂ) + ((y : ℚ) : ℂ) * I`, so that
`re` and `im` are read off by `Complex.ratCast_re` / `Complex.ratCast_im`.  No
complex division ever appears, hence no `starRingEnd` residue for `ring` to
choke on. -/

theorem s_rat : (s : ℚ) = 1 / 1000000 := by norm_num [s]

theorem a_Q : a = ((-329507 / 1600 : ℚ) : ℂ) + ((-1 / 1000000 : ℚ) : ℂ) * Complex.I := by
  unfold a; rw [A_value, s_rat] <;> push_cast <;> ring

theorem b_Q : b = ((9 / 5000000 : ℚ) : ℂ) + ((551827 / 800 : ℚ) : ℂ) * Complex.I := by
  unfold b; rw [B_value, s_rat] <;> push_cast <;> ring

theorem c_Q : c = ((23013813 / 32000 : ℚ) : ℂ) + ((-81 / 12500000 : ℚ) : ℂ) * Complex.I := by
  unfold c; rw [Cconst_value, s_rat] <;> push_cast <;> ring

theorem conj_a_Q :
    conj a = ((-329507 / 1600 : ℚ) : ℂ) + ((1 / 1000000 : ℚ) : ℂ) * Complex.I := by
  rw [conj_a, A_value, s_rat] <;> push_cast <;> ring

theorem conj_b_Q :
    conj b = ((9 / 5000000 : ℚ) : ℂ) + ((-551827 / 800 : ℚ) : ℂ) * Complex.I := by
  rw [conj_b, B_value, s_rat] <;> push_cast <;> ring

theorem conj_c_Q :
    conj c = ((23013813 / 32000 : ℚ) : ℂ) + ((81 / 12500000 : ℚ) : ℂ) * Complex.I := by
  rw [conj_c, Cconst_value, s_rat] <;> push_cast <;> ring

/-! ### Taylor coefficients of `Q'` at an arbitrary point

`Q'(w) = qp₀ + qp₁w + … + qp₆w⁶`; `qpTj v` is the `j`-th Taylor coefficient of
`Q'` at `v`.  The expansion lemma is the binomial theorem, so `ring` proves it
with `a`, `b`, `c`, their conjugates, `v` and `t` all atoms: no numeral and no
`I² = -1` is involved. -/

def qp0 : ℂ := c
def qp1 : ℂ := 2 * b
def qp2 : ℂ := 3 * a
def qp3 : ℂ := -4 * (s : ℂ) ^ 2 * conj a
def qp4 : ℂ := -5 * (s : ℂ) ^ 6 * conj b
def qp5 : ℂ := -6 * (s : ℂ) ^ 10 * conj c
def qp6 : ℂ := 7

theorem derivative_Q_eval' (w : ℂ) :
    (Polynomial.derivative Q).eval w
      = qp0 + qp1 * w + qp2 * w ^ 2 + qp3 * w ^ 3 + qp4 * w ^ 4 + qp5 * w ^ 5
        + qp6 * w ^ 6 := by
  rw [derivative_Q_eval]
  unfold qp0 qp1 qp2 qp3 qp4 qp5 qp6
  ring

def qpT0 (v : ℂ) : ℂ :=
  qp0 + qp1 * v + qp2 * v ^ 2 + qp3 * v ^ 3 + qp4 * v ^ 4 + qp5 * v ^ 5 + qp6 * v ^ 6
def qpT1 (v : ℂ) : ℂ :=
  qp1 + 2 * qp2 * v + 3 * qp3 * v ^ 2 + 4 * qp4 * v ^ 3 + 5 * qp5 * v ^ 4 + 6 * qp6 * v ^ 5
def qpT2 (v : ℂ) : ℂ :=
  qp2 + 3 * qp3 * v + 6 * qp4 * v ^ 2 + 10 * qp5 * v ^ 3 + 15 * qp6 * v ^ 4
def qpT3 (v : ℂ) : ℂ := qp3 + 4 * qp4 * v + 10 * qp5 * v ^ 2 + 20 * qp6 * v ^ 3
def qpT4 (v : ℂ) : ℂ := qp4 + 5 * qp5 * v + 15 * qp6 * v ^ 2
def qpT5 (v : ℂ) : ℂ := qp5 + 6 * qp6 * v
def qpT6 : ℂ := qp6

theorem Qp_taylor (v t : ℂ) :
    (Polynomial.derivative Q).eval (v + t)
      = qpT0 v + qpT1 v * t + qpT2 v * t ^ 2 + qpT3 v * t ^ 3 + qpT4 v * t ^ 4
        + qpT5 v * t ^ 5 + qpT6 * t ^ 6 := by
  rw [derivative_Q_eval']
  unfold qpT0 qpT1 qpT2 qpT3 qpT4 qpT5 qpT6
  ring

/-! ### Norm bounds through `normSq`; `Real.sqrt` never appears -/

theorem norm_le_of_normSq_le {z : ℂ} {n : ℝ} (hn : 0 ≤ n)
    (h : Complex.normSq z ≤ n ^ 2) : ‖z‖ ≤ n := by
  have h2 : ‖z‖ ^ 2 ≤ n ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hn, h2]

theorem le_norm_of_le_normSq {z : ℂ} {m : ℝ} (hm : 0 ≤ m)
    (h : m ^ 2 ≤ Complex.normSq z) : m ≤ ‖z‖ := by
  have h2 : m ^ 2 ≤ ‖z‖ ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hm, h2]

/-! ### The abstract disk localisation

A degree-six Taylor datum on a closed disk, with a residual bound and a
contraction bound, pins exactly one zero inside the disk.  This is the only
analytic step; every instance of it below supplies nothing but exact rational
inequalities. -/

theorem norm_pow_sub_pow_le (n : ℕ) {x y : ℂ} {rr : ℝ} (hx : ‖x‖ ≤ rr) (hy : ‖y‖ ≤ rr) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1) * rr ^ n * ‖x - y‖ := by
  have hr0 : (0 : ℝ) ≤ rr := le_trans (norm_nonneg x) hx
  induction n with
  | zero => simp
  | succ m ih =>
    have hfac : x ^ (m + 2) - y ^ (m + 2)
        = x * (x ^ (m + 1) - y ^ (m + 1)) + y ^ (m + 1) * (x - y) := by ring
    have hy' : ‖y ^ (m + 1)‖ ≤ rr ^ (m + 1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg y) hy _
    calc ‖x ^ (m + 2) - y ^ (m + 2)‖
        ≤ ‖x * (x ^ (m + 1) - y ^ (m + 1))‖ + ‖y ^ (m + 1) * (x - y)‖ := by
          rw [hfac]; exact norm_add_le _ _
      _ = ‖x‖ * ‖x ^ (m + 1) - y ^ (m + 1)‖ + ‖y ^ (m + 1)‖ * ‖x - y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ rr * ((m + 1) * rr ^ m * ‖x - y‖) + rr ^ (m + 1) * ‖x - y‖ := by
          have h1 : ‖x‖ * ‖x ^ (m + 1) - y ^ (m + 1)‖ ≤ rr * ((m + 1) * rr ^ m * ‖x - y‖) := by
            apply mul_le_mul hx ih (norm_nonneg _) hr0
          have h2 : ‖y ^ (m + 1)‖ * ‖x - y‖ ≤ rr ^ (m + 1) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right hy' (norm_nonneg _)
          linarith
      _ = (↑(m + 1) + 1) * rr ^ (m + 1) * ‖x - y‖ := by push_cast; ring

theorem newton_disk
    (p : ℂ → ℂ) {v d0 d1 d2 d3 d4 d5 d6 : ℂ} {rr n0 n2 n3 n4 n5 n6 m1 : ℝ}
    (hr : 0 < rr)
    (hexp : ∀ t : ℂ, p (v + t)
      = d0 + d1 * t + d2 * t ^ 2 + d3 * t ^ 3 + d4 * t ^ 4 + d5 * t ^ 5 + d6 * t ^ 6)
    (hn0 : ‖d0‖ ≤ n0) (hn2 : ‖d2‖ ≤ n2) (hn3 : ‖d3‖ ≤ n3) (hn4 : ‖d4‖ ≤ n4)
    (hn5 : ‖d5‖ ≤ n5) (hn6 : ‖d6‖ ≤ n6)
    (hm1 : m1 ≤ ‖d1‖) (hm1pos : 0 < m1)
    (hmapb : n0 + n2 * rr ^ 2 + n3 * rr ^ 3 + n4 * rr ^ 4 + n5 * rr ^ 5 + n6 * rr ^ 6
      ≤ m1 * rr)
    (hlipb : 2 * n2 * rr + 3 * n3 * rr ^ 2 + 4 * n4 * rr ^ 3 + 5 * n5 * rr ^ 4
      + 6 * n6 * rr ^ 5 ≤ m1 / 2) :
    ∃! z : ℂ, z ∈ Metric.closedBall v rr ∧ p z = 0 := by
  have hd1 : d1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm1
    linarith
  have hd1n : 0 < ‖d1‖ := lt_of_lt_of_le hm1pos hm1
  refine exists_unique_zero_of_newton_contraction p (Metric.closedBall v rr)
    (Metric.isClosed_closedBall.isComplete) v (Metric.mem_closedBall_self hr.le) d1 hd1
    ?_ ?_
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    have hzv : z = v + (z - v) := by ring
    have hpz := hexp (z - v)
    rw [← hzv] at hpz
    have hrew : z - p z / d1 - v
        = -((d0 + d2 * (z - v) ^ 2 + d3 * (z - v) ^ 3 + d4 * (z - v) ^ 4
            + d5 * (z - v) ^ 5 + d6 * (z - v) ^ 6) / d1) := by
      rw [hpz]; field_simp; ring
    rw [hrew, norm_neg, norm_div, div_le_iff₀ hd1n]
    have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn → ‖dd * (z - v) ^ k‖ ≤ nn * rr ^ k := by
      intro dd nn k hdd
      rw [norm_mul, norm_pow]
      exact mul_le_mul hdd (pow_le_pow_left₀ (norm_nonneg _) hz k) (by positivity)
        (le_trans (norm_nonneg _) hdd)
    have t2 := hb d2 n2 2 hn2
    have t3 := hb d3 n3 3 hn3
    have t4 := hb d4 n4 4 hn4
    have t5 := hb d5 n5 5 hn5
    have t6 := hb d6 n6 6 hn6
    have htri : ‖d0 + d2 * (z - v) ^ 2 + d3 * (z - v) ^ 3 + d4 * (z - v) ^ 4
        + d5 * (z - v) ^ 5 + d6 * (z - v) ^ 6‖
        ≤ ‖d0‖ + ‖d2 * (z - v) ^ 2‖ + ‖d3 * (z - v) ^ 3‖ + ‖d4 * (z - v) ^ 4‖
          + ‖d5 * (z - v) ^ 5‖ + ‖d6 * (z - v) ^ 6‖ := by
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      exact norm_add_le _ _
    nlinarith [htri, hn0, t2, t3, t4, t5, t6, hmapb, hm1, hr]
  · intro x hx y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hx hy
    have hpx := hexp (x - v)
    have hpy := hexp (y - v)
    rw [show v + (x - v) = x by ring] at hpx
    rw [show v + (y - v) = y by ring] at hpy
    have hrew : x - p x / d1 - (y - p y / d1)
        = -((d2 * ((x - v) ^ 2 - (y - v) ^ 2) + d3 * ((x - v) ^ 3 - (y - v) ^ 3)
            + d4 * ((x - v) ^ 4 - (y - v) ^ 4) + d5 * ((x - v) ^ 5 - (y - v) ^ 5)
            + d6 * ((x - v) ^ 6 - (y - v) ^ 6)) / d1) := by
      rw [hpx, hpy]; field_simp; ring
    have hxy : (x - v) - (y - v) = x - y := by ring
    have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn →
        ‖dd * ((x - v) ^ (k + 1) - (y - v) ^ (k + 1))‖
          ≤ nn * ((k + 1) * rr ^ k) * ‖x - y‖ := by
      intro dd nn k hdd
      rw [norm_mul]
      have h1 := norm_pow_sub_pow_le k hx hy
      rw [hxy] at h1
      have hnn : 0 ≤ nn := le_trans (norm_nonneg _) hdd
      calc ‖dd‖ * ‖(x - v) ^ (k + 1) - (y - v) ^ (k + 1)‖
          ≤ nn * ((k + 1) * rr ^ k * ‖x - y‖) :=
            mul_le_mul hdd h1 (norm_nonneg _) hnn
        _ = nn * ((k + 1) * rr ^ k) * ‖x - y‖ := by ring
    have t2 := hb d2 n2 1 hn2
    have t3 := hb d3 n3 2 hn3
    have t4 := hb d4 n4 3 hn4
    have t5 := hb d5 n5 4 hn5
    have t6 := hb d6 n6 5 hn6
    norm_num at t2 t3 t4 t5 t6
    rw [hrew, norm_neg, norm_div, div_le_iff₀ hd1n]
    have htri : ‖d2 * ((x - v) ^ 2 - (y - v) ^ 2) + d3 * ((x - v) ^ 3 - (y - v) ^ 3)
        + d4 * ((x - v) ^ 4 - (y - v) ^ 4) + d5 * ((x - v) ^ 5 - (y - v) ^ 5)
        + d6 * ((x - v) ^ 6 - (y - v) ^ 6)‖
        ≤ ‖d2 * ((x - v) ^ 2 - (y - v) ^ 2)‖ + ‖d3 * ((x - v) ^ 3 - (y - v) ^ 3)‖
          + ‖d4 * ((x - v) ^ 4 - (y - v) ^ 4)‖ + ‖d5 * ((x - v) ^ 5 - (y - v) ^ 5)‖
          + ‖d6 * ((x - v) ^ 6 - (y - v) ^ 6)‖ := by
      exact le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    simp only [norm_mul] at htri
    have hstep := le_trans htri
      (add_le_add (add_le_add (add_le_add (add_le_add t2 t3) t4) t5) t6)
    have p1 := mul_le_mul_of_nonneg_right hlipb (norm_nonneg (x - y))
    have p2 := mul_le_mul_of_nonneg_right hm1 (norm_nonneg (x - y))
    nlinarith [hstep, p1, p2, norm_nonneg (x - y)]

/-! ### `qp₀ … qp₆` as explicit Gaussian-rational numerals -/

theorem qp0_Q : qp0 = (((23013813 / 32000 : ℚ) : ℂ) + (((-81 / 12500000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp0
  rw [c_Q] <;> push_cast <;> ring

theorem qp1_Q : qp1 = (((9 / 2500000 : ℚ) : ℂ) + (((551827 / 400 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp1
  rw [b_Q] <;> push_cast <;> ring

theorem qp2_Q : qp2 = (((-988521 / 1600 : ℚ) : ℂ) + (((-3 / 1000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp2
  rw [a_Q] <;> push_cast <;> ring

theorem qp3_Q : qp3 = (((329507 / 400000000000000 : ℚ) : ℂ) + (((-1 / 250000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp3
  rw [conj_a_Q, s_rat] <;> push_cast <;> ring

theorem qp4_Q : qp4 = (((-9 / 1000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((551827 / 160000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp4
  rw [conj_b_Q, s_rat] <;> push_cast <;> ring

theorem qp5_Q : qp5 = (((-69041439 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-243 / 6250000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp5
  rw [conj_c_Q, s_rat] <;> push_cast <;> ring

theorem qp6_Q : qp6 = (((7 : ℚ) : ℂ) + (((0 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp6
  push_cast <;> ring

/-! ### Taylor coefficients of `Q` itself, for the `H_s` sign certificates -/

def qq0 : ℂ := 0
def qq1 : ℂ := c
def qq2 : ℂ := b
def qq3 : ℂ := a
def qq4 : ℂ := -(s : ℂ) ^ 2 * conj a
def qq5 : ℂ := -(s : ℂ) ^ 6 * conj b
def qq6 : ℂ := -(s : ℂ) ^ 10 * conj c
def qq7 : ℂ := 1



def qT0 (v : ℂ) : ℂ :=
  qq0 + qq1 * v + qq2 * v ^ 2 + qq3 * v ^ 3 + qq4 * v ^ 4 + qq5 * v ^ 5 + qq6 * v ^ 6
    + qq7 * v ^ 7
def qT1 (v : ℂ) : ℂ :=
  qq1 + 2 * qq2 * v + 3 * qq3 * v ^ 2 + 4 * qq4 * v ^ 3 + 5 * qq5 * v ^ 4 + 6 * qq6 * v ^ 5
    + 7 * qq7 * v ^ 6
def qT2 (v : ℂ) : ℂ :=
  qq2 + 3 * qq3 * v + 6 * qq4 * v ^ 2 + 10 * qq5 * v ^ 3 + 15 * qq6 * v ^ 4 + 21 * qq7 * v ^ 5
def qT3 (v : ℂ) : ℂ :=
  qq3 + 4 * qq4 * v + 10 * qq5 * v ^ 2 + 20 * qq6 * v ^ 3 + 35 * qq7 * v ^ 4
def qT4 (v : ℂ) : ℂ := qq4 + 5 * qq5 * v + 15 * qq6 * v ^ 2 + 35 * qq7 * v ^ 3
def qT5 (v : ℂ) : ℂ := qq5 + 6 * qq6 * v + 21 * qq7 * v ^ 2
def qT6 (v : ℂ) : ℂ := qq6 + 7 * qq7 * v
def qT7 : ℂ := qq7







/-! ### `K₀` is between `0` and `10⁻¹¹` -/

















/-! ### `qq₀ … qq₇` as explicit Gaussian-rational numerals -/

















theorem qpT6_bound : ‖qpT6‖ ≤ (7 : ℝ) := by
  unfold qpT6
  rw [qp6_Q]
  apply norm_le_of_normSq_le (by norm_num)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im]
  push_cast
  norm_num

/-! ### Centre 0: the critical point near `+3.18983-0.50000 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 9.525e-11 against the radius,
contraction ≤ 2.057e-06 against `1/2`. -/

def vc0 : ℂ := (((15949137893 / 5000000000 : ℚ) : ℂ) + (((-4999999979 / 10000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc0_p2 : vc0 ^ 2 = (((198499999665942783471 / 20000000000000000000 : ℚ) : ℂ) + (((-79745689130068104247 / 25000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 2 = vc0 ^ 1 * vc0 := by ring
  rw [hs]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p3 : vc0 ^ 3 = (((15032062444211514848128961211389 / 500000000000000000000000000000 : ℚ) : ℂ) + (((-15137499909268208878783023188113 / 1000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 3 = vc0 ^ 2 * vc0 := by ring
  rw [hs, vc0_p2]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p4 : vc0 ^ 4 = (((883306247727210733585620292143044419203881 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-15829519265678895752052017655043376501337 / 250000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 4 = vc0 ^ 3 * vc0 := by ring
  rw [hs, vc0_p3]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p5 : vc0 ^ 5 = (((12505021226830210354606678811685869687691313480324273 / 50000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-24613906063943647314412641438549781458306649145753779 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 5 = vc0 ^ 4 * vc0 := by ring
  rw [hs, vc0_p4]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p6 : vc0 ^ 6 = (((134941540360720403149205355799054764942496515791919405357747303 / 200000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-227547843885365856204262660608742721908300340732250729305018957 / 250000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 6 = vc0 ^ 5 * vc0 := by ring
  rw [hs, vc0_p5]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc0_bound : ‖qpT0 vc0‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc0_bound : ‖qpT2 vc0‖ ≤ (2728815463 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc0_bound : ‖qpT3 vc0‖ ≤ (4712399811 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc0_bound : ‖qpT4 vc0‖ ≤ (547312499 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc0_bound : ‖qpT5 vc0‖ ≤ (33902157 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc0_lower : (5306414501 / 500000 : ℝ) ≤ ‖qpT1 vc0‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc0`. -/
theorem crit_loc_0 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc0 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc0 t)
    qpT0_vc0_bound qpT2_vc0_bound qpT3_vc0_bound qpT4_vc0_bound qpT5_vc0_bound
    qpT6_bound qpT1_vc0_lower (by norm_num) (by norm_num) (by norm_num)























/-! ### Centre 1: the critical point near `-3.18983-0.50000 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 9.525e-11 against the radius,
contraction ≤ 2.057e-06 against `1/2`. -/

def vc1 : ℂ := (((-6379655169 / 2000000000 : ℚ) : ℂ) + (((-5000000021 / 10000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc1_p2 : vc1 ^ 2 = (((31015625052303451987 / 3125000000000000000 : ℚ) : ℂ) + (((31898275978972758549 / 10000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 2 = vc1 ^ 1 * vc1 := by ring
  rw [hs]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p3 : vc1 ^ 3 = (((-3006412502390370216903098003319 / 100000000000000000000000000000 : ℚ) : ℂ) + (((-7568750045391578536216879612157 / 500000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 3 = vc1 ^ 2 * vc1 := by ring
  rw [hs, vc1_p2]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p4 : vc1 ^ 4 = (((220826563069811055808964980701675732896239 / 2500000000000000000000000000000000000000 : ℚ) : ℂ) + (((989344967578716910505605223348565286863 / 15625000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 4 = vc1 ^ 3 * vc1 := by ring
  rw [hs, vc1_p3]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p5 : vc1 ^ 5 = (((-250100425812678017230243263215578736069007720847491 / 1000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-6153476609056572105506692888783902476071989986698619 / 25000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 5 = vc1 ^ 4 * vc1 := by ring
  rw [hs, vc1_p4]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p6 : vc1 ^ 6 = (((5271153941050411655522736984469585705197486842021741957287543 / 7812500000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((22754784763932923793702130020795388297412765021595585818749083 / 25000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 6 = vc1 ^ 5 * vc1 := by ring
  rw [hs, vc1_p5]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc1_bound : ‖qpT0 vc1‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc1_bound : ‖qpT2 vc1‖ ≤ (10915261941 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc1_bound : ‖qpT3 vc1‖ ≤ (4712399839 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc1_bound : ‖qpT4 vc1‖ ≤ (1094625003 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc1_bound : ‖qpT5 vc1‖ ≤ (135608629 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc1_lower : (5306414559 / 500000 : ℝ) ≤ ‖qpT1 vc1‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc1`. -/
theorem crit_loc_1 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc1 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc1 t)
    qpT0_vc1_bound qpT2_vc1_bound qpT3_vc1_bound qpT4_vc1_bound qpT5_vc1_bound
    qpT6_bound qpT1_vc1_lower (by norm_num) (by norm_num) (by norm_num)























/-! ### Centre 2: the critical point near `+0.00000+0.82325 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.646e-09 against the radius,
contraction ≤ 3.012e-06 against `1/2`. -/

def vc2 : ℂ := (((39 / 10000000000 : ℚ) : ℂ) + (((4116237331 / 5000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc2_p2 : vc2 ^ 2 = (((-67773639060472012723 / 100000000000000000000 : ℚ) : ℂ) + (((160533255909 / 25000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 2 = vc2 ^ 1 * vc2 := by ring
  rw [hs]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p3 : vc2 ^ 3 = (((-7929515770075225607229 / 1000000000000000000000000000000 : ℚ) : ℂ) + (((-278972383158434652729525601411 / 500000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 3 = vc2 ^ 2 * vc2 := by ring
  rw [hs, vc2_p2]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p4 : vc2 ^ 4 = (((4593266151499137311106062272858939214233 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-10879922943178951944793662930207 / 1250000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 4 = vc2 ^ 3 * vc2 := by ring
  rw [hs, vc2_p3]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p5 : vc2 ^ 5 = (((895686899542331856070972051770281044675359 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((18906973604019448917001755292036170302874264019831 / 50000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 5 = vc2 ^ 4 * vc2 := by ring
  rw [hs, vc2_p4]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p6 : vc2 ^ 6 = (((-311302362260385834197051500751481978043948469589353203705243 / 1000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((2212115911670275854256461300671953057133243894200119 / 250000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 6 = vc2 ^ 5 * vc2 := by ring
  rw [hs, vc2_p5]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc2_bound : ‖qpT0 vc2‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc2_bound : ‖qpT2 vc2‖ ≤ (569596331 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc2_bound : ‖qpT3 vc2‖ ≤ (19528067 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc2_bound : ‖qpT4 vc2‖ ≤ (35581161 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc2_bound : ‖qpT5 vc2‖ ≤ (17288197 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc2_lower : (378202597 / 1000000 : ℝ) ≤ ‖qpT1 vc2‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc2`. -/
theorem crit_loc_2 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc2 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc2 t)
    qpT0_vc2_bound qpT2_vc2_bound qpT3_vc2_bound qpT4_vc2_bound qpT5_vc2_bound
    qpT6_bound qpT1_vc2_lower (by norm_num) (by norm_num) (by norm_num)

























/-! ### Centre 3: the critical point near `+0.00000+1.80786 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.315e-08 against the radius,
contraction ≤ 2.331e-05 against `1/2`. -/

def vc3 : ℂ := (((1137 / 5000000000 : ℚ) : ℂ) + (((9039295429 / 5000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc3_p2 : vc3 ^ 2 = (((-10213607731592375159 / 3125000000000000000 : ℚ) : ℂ) + (((10277678902773 / 12500000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 2 = vc3 ^ 1 * vc3 := by ring
  rw [hs]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p3 : vc3 ^ 3 = (((-139354463889847836547749 / 62500000000000000000000000000 : ℚ) : ℂ) + (((-369295270727116376943094939943 / 62500000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 3 = vc3 ^ 2 * vc3 := by ring
  rw [hs, vc3_p2]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p4 : vc3 ^ 4 = (((1669084526317391063213658163374817314967 / 156250000000000000000000000000000000000 : ℚ) : ℂ) + (((-104972180704186151812244101415907 / 19531250000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 4 = vc3 ^ 3 * vc3 := by ring
  rw [hs, vc3_p3]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p5 : vc3 ^ 5 = (((9488745532114968704806074709045331871030303 / 781250000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((15087348129354468413956985009325637196544777295771 / 781250000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 5 = vc3 ^ 4 * vc3 := by ring
  rw [hs, vc3_p4]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p6 : vc3 ^ 6 = (((-17047374622674344793917029959750173772036924432643552484531 / 488281250000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((51462944469233519951250346702254611414031823606838307 / 1953125000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 6 = vc3 ^ 5 * vc3 := by ring
  rw [hs, vc3_p5]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc3_bound : ‖qpT0 vc3‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc3_bound : ‖qpT2 vc3‖ ≤ (503799177 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc3_bound : ‖qpT3 vc3‖ ≤ (827221407 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc3_bound : ‖qpT4 vc3‖ ≤ (17158861 / 50000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc3_bound : ‖qpT5 vc3‖ ≤ (37965041 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc3_lower : (43220003 / 1000000 : ℝ) ≤ ‖qpT1 vc3‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc3`. -/
theorem crit_loc_3 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc3 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc3 t)
    qpT0_vc3_bound qpT2_vc3_bound qpT3_vc3_bound qpT4_vc3_bound qpT5_vc3_bound
    qpT6_bound qpT1_vc3_lower (by norm_num) (by norm_num) (by norm_num)























/-! ### Centre 4: the critical point near `-0.00000+1.88386 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.072e-08 against the radius,
contraction ≤ 2.917e-05 against `1/2`. -/

def vc4 : ℂ := (((-453 / 2000000000 : ℚ) : ℂ) + (((3767718291 / 2000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc4_p2 : vc4 ^ 2 = (((-887231320020984717 / 250000000000000000 : ℚ) : ℂ) + (((-1706776385823 / 2000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 2 = vc4 ^ 1 * vc4 := by ring
  rw [hs]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p3 : vc4 ^ 3 = (((9645978911268238802901 / 4000000000000000000000000000 : ℚ) : ℂ) + (((-26742701382328335806876091357 / 4000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 3 = vc4 ^ 2 * vc4 := by ring
  rw [hs, vc4_p2]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p4 : vc4 ^ 4 = (((50379482574472542679355244232089098367 / 4000000000000000000000000000000000000 : ℚ) : ℂ) + (((1514305465774385795798778467091 / 250000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 4 = vc4 ^ 3 * vc4 := by ring
  rw [hs, vc4_p3]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p5 : vc4 ^ 5 = (((-114109528031186907307694303011787597743947 / 8000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((189815697986944993044268969031766395512714655229 / 8000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 5 = vc4 ^ 4 * vc4 := by ring
  rw [hs, vc4_p4]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p6 : vc4 ^ 6 = (((-44698254826518302367972614979730526430820686861767755353 / 1000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-257959533564283105475987616732699348897039592626657 / 8000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 6 = vc4 ^ 5 * vc4 := by ring
  rw [hs, vc4_p5]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc4_bound : ‖qpT0 vc4‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc4_bound : ‖qpT2 vc4‖ ≤ (704635793 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc4_bound : ‖qpT3 vc4‖ ≤ (935994549 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc4_bound : ‖qpT4 vc4‖ ≤ (74527431 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc4_bound : ‖qpT5 vc4‖ ≤ (15824417 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc4_lower : (24153503 / 500000 : ℝ) ≤ ‖qpT1 vc4‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc4`. -/
theorem crit_loc_4 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc4 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc4 t)
    qpT0_vc4_bound qpT2_vc4_bound qpT3_vc4_bound qpT4_vc4_bound qpT5_vc4_bound
    qpT6_bound qpT1_vc4_lower (by norm_num) (by norm_num) (by norm_num)























/-! ### Centre 5: the critical point near `+0.00000-3.51497 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 6.040e-11 against the radius,
contraction ≤ 1.833e-06 against `1/2`. -/

def vc5 : ℂ := (((11 / 10000000000 : ℚ) : ℂ) + (((-2196853561 / 625000000 : ℚ) : ℂ)) * Complex.I)

theorem vc5_p2 : vc5 ^ 2 = (((-247099677106093092891 / 20000000000000000000 : ℚ) : ℂ) + (((-24165389171 / 3125000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 2 = vc5 ^ 1 * vc5 := by ring
  rw [hs]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p3 : vc5 ^ 3 = (((-40771446722505360329677 / 1000000000000000000000000000000 : ℚ) : ℂ) + (((2714209027862353929043847112493 / 62500000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 3 = vc5 ^ 2 * vc5 := by ring
  rw [hs, vc5_p2]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p4 : vc5 ^ 4 = (((1526456260648386673948267200732713583592241 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((5971259861297178645066068483361 / 31250000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 4 = vc5 ^ 3 * vc5 := by ring
  rw [hs, vc5_p3]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p5 : vc5 ^ 5 = (((83955094335661267100043663063120237763942171 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-3353400871916152432254519560223784343393150746480781 / 6250000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 5 = vc5 ^ 4 * vc5 := by ring
  rw [hs, vc5_p4]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p6 : vc5 ^ 6 = (((-377186849122790623263217003237700071473883591330440409164377643 / 200000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-110662228773233030336651389809080744940103846985354761 / 31250000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 6 = vc5 ^ 5 * vc5 := by ring
  rw [hs, vc5_p5]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)



theorem qpT0_vc5_bound : ‖qpT0 vc5‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc5_bound : ‖qpT2 vc5‖ ≤ (1926245639 / 125000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc5_bound : ‖qpT3 vc5‖ ≤ (6079828223 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc5_bound : ‖qpT4 vc5‖ ≤ (259454661 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc5_bound : ‖qpT5 vc5‖ ≤ (1845357 / 12500 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc5_lower : (16812014601 / 1000000 : ℝ) ≤ ‖qpT1 vc5‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc5`. -/
theorem crit_loc_5 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc5 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc5 t)
    qpT0_vc5_bound qpT2_vc5_bound qpT3_vc5_bound qpT4_vc5_bound qpT5_vc5_bound
    qpT6_bound qpT1_vc5_lower (by norm_num) (by norm_num) (by norm_num)























end Erdos1041.Counterexample.S4Proofs
-- END GENERATED

/-! ## Assembly of `s4_instance_critical`

Hand-authored; regenerate with
`./repo-python formal_math/erdos1041_external_counterexample/emit_s4_assembly.py`. -/

noncomputable section
open scoped ComplexConjugate NNReal
namespace Erdos1041.Counterexample.S4Proofs

set_option maxHeartbeats 4000000

/-! ### The six disks are pairwise disjoint

The centres are more than `2·10⁻⁶` apart (in fact more than `0.07`), so the six
closed disks of radius `10⁻⁶` are disjoint and the six localised zeros are
distinct. -/

































/-! ### The six critical points, extracted from the localisation certificates -/

noncomputable def zc0 : ℂ := crit_loc_0.choose







noncomputable def zc1 : ℂ := crit_loc_1.choose







noncomputable def zc2 : ℂ := crit_loc_2.choose







noncomputable def zc3 : ℂ := crit_loc_3.choose







noncomputable def zc4 : ℂ := crit_loc_4.choose







noncomputable def zc5 : ℂ := crit_loc_5.choose







/-! ### The six critical points of `f`, and their distinctness -/





def cf0 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc0



def cf1 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc1



def cf2 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc2



def cf3 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc3



def cf4 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc4



def cf5 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc5

































/-- The six critical points of `f` as a multiset. -/
def critMul : Multiset ℂ := {cf0, cf1, cf2, cf3, cf4, cf5}








/-! ### Exhaustion of `derivative f` -/









/-! ### `H_s` decides membership of `Ω(f)` -/





/-! ### An upper bound for `H_s` on a disk -/




/-! ### The interior critical point and its data -/

def zs : ℂ := (ρ : ℂ) * (ε : ℂ) * zc2



















/-! ### `zs` is localised at `ρε·(823247/10⁶)i` -/



/-! ### Simplicity and global uniqueness -/





/-! ### The two remaining certificates

Both are exact-rational estimates verified in `instance_certificates_coarse.py`,
and both are now formalised: `s4_projection` below (Cauchy-Schwarz plus the
tightened Cayley enclosures) and `s4_disk_package` (the explicit identification
of `shiftQuad f zs`). -/

/-! ### Step 4: the disk criterion at `zs`

`shiftQuad f zs` is defined by division, so its coefficients are not writable.
It is identified with an explicit polynomial `Apoly` by `shiftQuad_spec`,
`Polynomial.funext` and cancellation of `X²`.  The Taylor data is transported
from `vc2` to `zc2` by the shift identity
`qTj (v + τ) = Σ_{m ≥ j} C(m,j) · qTm v · τ^{m-j}`, a `ring` identity with
`v` and `τ` atoms. -/























/-! #### Taylor bounds at `zc2` -/











/-! #### The explicit comparison polynomial -/

def Apoly : Polynomial ℂ :=
  Polynomial.C (qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5)
    + Polynomial.C (qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4) * Polynomial.X
    + Polynomial.C (qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3) * Polynomial.X ^ 2
    + Polynomial.C (qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2) * Polynomial.X ^ 3
    + Polynomial.C (qT6 zc2 * (ρ : ℂ) * (ε : ℂ)) * Polynomial.X ^ 4
    + Polynomial.C qT7 * Polynomial.X ^ 5











/-! #### The comparison coefficient and the disk bound -/

def aHat : ℂ := qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5
















/-! ### Step 5: the projection bound

`‖ζ‖ = 1` gives `‖ζ − εq‖ ≥ 1 − ε·Re(ζ·conj q)` by Cauchy–Schwarz, so the sum of
the two distances is at least `2 − ε(R₃+R₆)`.  The certificate is
`R₃ + R₆ ≤ −0.2735` against the demanded `−0.143`. -/









/-! #### Componentwise enclosures -/







/-! #### The projection certificate -/













end Erdos1041.Counterexample.S4Proofs

namespace Erdos1041.Counterexample



end Erdos1041.Counterexample


