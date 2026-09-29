-- Prove2me | Definitions.Def_Kepler_NonlinearCatalogModel
-- name    : Kepler_NonlinearCatalogModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:55:29.638741+00:00
-- url     : https://prove2.me/theorems/f8de56d3-30a8-4e70-9e1a-6bdbb97cad72
-- title:
--   Exact nonlinear catalog and certificate contracts
-- statement:
--   This module defines explicit real arithmetic and analytic functions, a finite catalog of real implications, and a general conditional certificate interface. Its square root is the signed extension $S(x)=\sqrt{x}$ for $x\geq0$ and $-\sqrt{-x}$ for $x<0$. Its logarithm classically chooses $y$ with $\exp y=x$, with no specified numerical value when $x\leq0$; the constant $h_-$ similarly selects a root of the displayed quartic-weight equality in $[6/5,13/10)$, without a supplied existence or uniqueness proof. Arithmetic is total, including division by zero. The angle function A uses four explicit arctangent branches and has $A(0,0)=\pi$; the nonlinear dihedral formula consequently gives $3\pi/2$ on the zero six-tuple. The catalog formulas are the specified polynomials, signed roots, quotients, inverse trigonometric expressions, permutations and substitutions, and weighted angle and volume expressions, with no geometric validity assumed merely from a function's name. The catalog concatenates lists of sizes 81, 230, 109, 127, 5, and 28, covering 539 distinct problems in 580 occurrences. Each problem requires its full written conclusion for every real vector in its specified closed interval domain; the distinct arities are 1, 5, 6, 9, and 10. Domains include boundaries and fixed coordinates, and may be empty; conclusions can be disjunctions rather than a single inequality. CatalogValid universally requires all these implications. The separate encoded language has rational boxes, real arithmetic expressions, logical formulas, and finite certificate trees containing proposed interval or Taylor data, splits, and monotonicity nodes. A checker is an arbitrary Boolean-valued function on these data. Soundness means every accepted encoded problem is valid. Certification requires an exact domain encoding, equivalence of conclusions on that domain, and an accepted certificate for each catalog member. The two supplied theorem proofs establish only that a sound checker plus such a certified family implies catalog validity. The module supplies no specific checker, proof of a concrete checker's soundness, completed certificate family, or proof that CatalogValid itself holds.
--
--   **Source and scope.** Primary §§5–6, pp.12–17; general/the_main_statement.hl:55–59 and the six cited selectors. All 539 selected source-ID records are present; interval/Taylor syntax and checker soundness are separate from validity.
--
--   **Forensic count audit.** These 539 source IDs have 498 distinct normalized syntactic bodies; repeated formulas are retained, and no claim of semantic inequivalence is made. All 539 domains have separately kernel-checked witnesses; this does not prove the inequalities.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §§5–6, pp.12–17; general/the_main_statement.hl:55–59 and the six cited selectors. All 539 selected source-ID records are present; interval/Taylor syntax and checker soundness are separate from validity.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

/-
Flyspeck source material is reproduced and adapted under this license:
MIT License

Copyright (c) 2014 Thomas C. Hales

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

noncomputable section

namespace KeplerMission.Nonlinear

/- Transparent scalar definitions translated from official Flyspeck sphere.hl at
1ce0353008eba83d3c76ae9a25c3c242e4802d53. Names follow the source for the audit map.
HOL Light real.ml defines a signed square root; using Real.sqrt on negative
arguments would change source formulas. Logarithm uses the source choice predicate. -/

def holSqrt (x : ℝ) : ℝ := if 0 ≤ x then Real.sqrt x else -Real.sqrt (-x)

def holLog (x : ℝ) : ℝ := Classical.epsilon (fun y : ℝ ↦ Real.exp y = x)

def atn2 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y) else Real.pi

def sqrt8 : ℝ := holSqrt 8
def sqrt2 : ℝ := holSqrt 2
def sqrt3 : ℝ := holSqrt 3
def pi_rt18 : ℝ := Real.pi / holSqrt 18

def delta_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
  x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
  x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
  x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

def delta_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  delta_x (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

def abc_of_quadratic (f : ℝ → ℝ) : ℝ × ℝ × ℝ :=
  let c := f 0
  let p := f 1
  let n := f (-1)
  ((p + n) / 2 - c, (p - n) / 2, c)

def quadratic_root_plus (q : ℝ × ℝ × ℝ) : ℝ :=
  (-q.2.1 + holSqrt (q.2.1 ^ 2 - 4 * q.1 * q.2.2)) / (2 * q.1)

def edge_flat (y1 y2 y3 y5 y6 : ℝ) : ℝ :=
  holSqrt (quadratic_root_plus (abc_of_quadratic
    (fun x4 ↦ -delta_x (y1 * y1) (y2 * y2) (y3 * y3) x4 (y5 * y5) (y6 * y6))))

def edge_flat2_x (x1 x2 x3 _x4 x5 x6 : ℝ) : ℝ :=
  (edge_flat (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x5) (holSqrt x6)) ^ 2

def edge_flat_x (x1 x2 x3 _x4 x5 x6 : ℝ) : ℝ :=
  edge_flat (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x5) (holSqrt x6)

def delta_x4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

def delta_x6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x2 - x3 * x6 + x1 * x4 + x2 * x5 - x4 * x5 +
    x3 * (-x3 + x1 + x2 - x6 + x4 + x5)

def ups_x (x1 x2 x6 : ℝ) : ℝ :=
  -x1 * x1 - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

def eta_x (x1 x2 x3 : ℝ) : ℝ := holSqrt (x1 * x2 * x3 / ups_x x1 x2 x3)
def eta_y (y1 y2 y3 : ℝ) : ℝ := eta_x (y1 * y1) (y2 * y2) (y3 * y3)

def rho_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x1 * x4 * x4 - x2 * x2 * x5 * x5 - x3 * x3 * x6 * x6 +
    2 * x1 * x2 * x4 * x5 + 2 * x1 * x3 * x4 * x6 + 2 * x2 * x3 * x5 * x6

def chi_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -(x1 * x4 * x4) + x1 * x4 * x5 + x2 * x4 * x5 - x2 * x5 * x5 +
    x1 * x4 * x6 + x3 * x4 * x6 + x2 * x5 * x6 + x3 * x5 * x6 -
    2 * x4 * x5 * x6 - x3 * x6 * x6

def dih_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + atn2 (holSqrt (4 * x1 * delta_x x1 x2 x3 x4 x5 x6))
    (-delta_x4 x1 x2 x3 x4 x5 x6)

def dih_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dih_x (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

def dih2_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := dih_y y2 y1 y3 y5 y4 y6
def dih3_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := dih_y y3 y1 y2 y6 y4 y5
def dih2_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := dih_x x2 x1 x3 x5 x4 x6
def dih3_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := dih_x x3 x1 x2 x6 x4 x5
def dih4_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := dih_y y4 y2 y6 y1 y5 y3
def dih5_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := dih_y y5 y1 y6 y2 y4 y3
def dih6_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := dih_y y6 y1 y5 y3 y4 y2

def sol_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  dih_x x1 x2 x3 x4 x5 x6 + dih_x x2 x3 x1 x5 x6 x4 +
    dih_x x3 x1 x2 x6 x4 x5 - Real.pi

def sol_y (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dih_y y1 y2 y3 y4 y5 y6 + dih_y y2 y3 y1 y5 y6 y4 +
    dih_y y3 y1 y2 y6 y4 y5 - Real.pi

def interp (x1 y1 x2 y2 x : ℝ) : ℝ := y1 + (x - x1) * (y2 - y1) / (x2 - x1)
def const1 : ℝ := sol_y 2 2 2 2 2 2 / Real.pi
def ly (y : ℝ) : ℝ := interp 2 1 (63 / 25) 0 y
def rho (y : ℝ) : ℝ := 1 + const1 - const1 * ly y
def h0 : ℝ := 63 / 50
def rh0 : ℝ := 1 / (h0 - 1)
def sol0 : ℝ := 3 * Real.arccos (1 / 3) - Real.pi
def rho_fun (y : ℝ) : ℝ := 1 + (2 * h0 - 2)⁻¹ * Real.pi⁻¹ * sol0 * (y - 2)
def rhazim (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := rho y1 * dih_y y1 y2 y3 y4 y5 y6
def lnazim (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := ly y1 * dih_y y1 y2 y3 y4 y5 y6

def taum (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  sol_y y1 y2 y3 y4 y5 y6 * (1 + const1) - const1 *
    (lnazim y1 y2 y3 y4 y5 y6 + lnazim y2 y3 y1 y5 y6 y4 + lnazim y3 y1 y2 y6 y4 y5)

abbrev Scalar6 := ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
def node2_y (f : Scalar6) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := f y2 y3 y1 y5 y6 y4
def node3_y (f : Scalar6) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := f y3 y1 y2 y6 y4 y5
def rhazim2 : Scalar6 := node2_y rhazim
def rhazim3 : Scalar6 := node3_y rhazim
def rhazim4 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := rho y4 * dih4_y y1 y2 y3 y4 y5 y6
def rhazim5 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := rho y5 * dih5_y y1 y2 y3 y4 y5 y6
def rhazim6 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := rho y6 * dih6_y y1 y2 y3 y4 y5 y6

def tauq (y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ) : ℝ :=
  taum y1 y2 y3 y4 y5 y6 + taum y7 y2 y3 y4 y8 y9

def vol_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := holSqrt (delta_x x1 x2 x3 x4 x5 x6) / 12
def arclength (a b c : ℝ) : ℝ :=
  Real.pi / 2 + atn2 (holSqrt (ups_x (a * a) (b * b) (c * c))) (c * c - a * a - b * b)
def volR (a b c : ℝ) : ℝ := holSqrt (a * a * (b * b - a * a) * (c * c - b * b)) / 6
def solR (a b c : ℝ) : ℝ := 2 * atn2 (holSqrt ((c + b) * (b + a)))
  (holSqrt ((c - b) * (b - a)))
def dihR (a b c : ℝ) : ℝ := atn2 (holSqrt (b * b - a * a)) (holSqrt (c * c - b * b))
def rad2_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rho_x x1 x2 x3 x4 x5 x6 / (delta_x x1 x2 x3 x4 x5 x6 * 4)

def tau0 : ℝ := 4 * Real.pi - 20 * sol0
def mm1 : ℝ := sol0 * holSqrt 8 / tau0
def mm2 : ℝ := (6 * sol0 - Real.pi) * holSqrt 2 / (6 * tau0)
def hplus : ℝ := 6627 / 5000
def h0cut (y : ℝ) : ℝ := if y ≤ 2 * h0 then 1 else 0
def marchal_quartic (h : ℝ) : ℝ :=
  (holSqrt 2 - h) * (h - hplus) * (9 * h ^ 2 - 17 * h + 3) /
    ((holSqrt 2 - 1) * 5 * (hplus - 1))
def lmfun (h : ℝ) : ℝ := if h ≤ h0 then (h0 - h) / (h0 - 1) else 0
def lfun (h : ℝ) : ℝ := (h0 - h) / (h0 - 1)
def flat_term (y : ℝ) : ℝ := sol0 * (y - 2 * h0) / (2 * h0 - 2)
def hminus : ℝ := Classical.epsilon
  (fun x : ℝ ↦ 6 / 5 ≤ x ∧ x < 13 / 10 ∧ marchal_quartic x = lmfun x)
def cstab : ℝ := 301 / 100

def y_of_x (f : Scalar6) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  f (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
def rad2_y : Scalar6 := y_of_x rad2_x
def delta4_y : Scalar6 := y_of_x delta_x4
def vol_y : Scalar6 := y_of_x vol_x

def vol4f (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (sol_y y1 y2 y3 y4 y5 y6 + sol_y y1 y5 y6 y4 y2 y3 +
      sol_y y4 y5 y3 y1 y2 y6 + sol_y y4 y2 y6 y1 y5 y3) -
  (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dih_y y1 y2 y3 y4 y5 y6 +
      f (y2 / 2) * dih_y y2 y3 y1 y5 y6 y4 +
      f (y3 / 2) * dih_y y3 y1 y2 y6 y4 y5 +
      f (y4 / 2) * dih_y y4 y3 y5 y1 y6 y2 +
      f (y5 / 2) * dih_y y5 y1 y6 y2 y4 y3 +
      f (y6 / 2) * dih_y y6 y1 y5 y3 y4 y2)

def gamma4f (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  vol_y y1 y2 y3 y4 y5 y6 - vol4f y1 y2 y3 y4 y5 y6 f
def gamma4fgcy := gamma4f
def vol3r (y1 y2 y3 r : ℝ) : ℝ := vol_y r r r y1 y2 y3
def vol3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (sol_y y1 y2 r r r y3 + sol_y y2 y3 r r r y1 + sol_y y3 y1 r r r y2) -
  (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dih_y y1 y2 r r r y3 + f (y2 / 2) * dih_y y2 y3 r r r y1 +
      f (y3 / 2) * dih_y y3 y1 r r r y2)
def gamma3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  vol3r y1 y2 y3 r - vol3f y1 y2 y3 r f

/- Preserve this exact source formula, including its normalization; do not repair
the historical source comment about the name's geometric interpretation. -/
def vol2r (y r : ℝ) : ℝ := 2 * Real.pi * (r * r - (y / 2) ^ 2) / 3
def vol2f (y r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) * 2 * Real.pi * (1 - y / (r * 2)) -
    (8 * mm2 / Real.pi) * 2 * Real.pi * f (y / 2)

def norm2hh (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (y1 - hminus - hplus) ^ 2 + (y2 - 2) ^ 2 + (y3 - 2) ^ 2 +
    (y4 - 2) ^ 2 + (y5 - 2) ^ 2 + (y6 - 2) ^ 2
def bump (h : ℝ) : ℝ := (1 / 200) * (1 - (h - h0) ^ 2 / (hplus - h0) ^ 2)
def critical_edge_y (y : ℝ) : Prop := 2 * hminus ≤ y ∧ y ≤ 2 * hplus
def beta_bump_force_y (y1 _y2 _y3 y4 _y5 _y6 : ℝ) : ℝ := bump (y1 / 2) - bump (y4 / 2)
def a_spine5 : ℝ := 112061 / 2000000
def b_spine5 : ℝ := -(445813 / 10000000)
def beta_bump_lb : ℝ := -(1 / 200)
def machine_eps : ℝ := 0

def gamma23f (y1 y2 y3 y4 y5 y6 : ℝ) (w1 w2 : ℕ) (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  gamma3f y1 y2 y6 r f / w1 + gamma3f y1 y3 y5 r f / w2 +
    (dih_y y1 y2 y3 y4 y5 y6 - dih_y y1 y2 r r r y6 - dih_y y1 y3 r r r y5) *
      (vol2r y1 r - vol2f y1 r f) / (2 * Real.pi)
def gamma23f_126_03 (y1 y2 y3 y4 y5 y6 : ℝ) (w1 : ℕ) (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  gamma3f y1 y2 y6 r f / w1 +
    (dih_y y1 y2 y3 y4 y5 y6 - dih_y y1 y2 r r r y6 - 3 / 100) *
      (vol2r y1 r - vol2f y1 r f) / (2 * Real.pi)
def gamma23f_red_03 (y1 y2 y3 y4 y5 y6 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (dih_y y1 y2 y3 y4 y5 y6 - 2 * (3 / 100)) * (vol2r y1 r - vol2f y1 r f) /
    (2 * Real.pi)

def rotate2 (f : Scalar6) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  f x2 x3 x1 x5 x6 x4

def rotate3 (f : Scalar6) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  f x3 x1 x2 x6 x4 x5

def rotate4 (f : Scalar6) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  f x4 x2 x6 x1 x5 x3

def rotate5 (f : Scalar6) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  f x5 x3 x4 x2 x6 x1

def rotate6 (f : Scalar6) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  f x6 x1 x5 x3 x4 x2

def norm2hh_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  norm2hh (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def rhazim_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhazim (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def rhazim2_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhazim2 (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def rhazim3_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhazim3 (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def dih4_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  dih4_y (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def dih5_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  dih5_y (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def dih6_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  dih6_y (holSqrt x1) (holSqrt x2) (holSqrt x3) (holSqrt x4) (holSqrt x5) (holSqrt x6)

def gcy (y : ℝ) : ℝ :=
  4 * mm1 / Real.pi - (8 * mm2 / Real.pi) * lmfun (y / 2)

def gchi (y : ℝ) : ℝ :=
  4 * mm1 / Real.pi - 504 * (mm2 / Real.pi) / 13 + 200 * y * (mm2 / Real.pi) / 13

def gchi1_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x1) * dih_x x1 x2 x3 x4 x5 x6

def gchi2_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x2) * dih2_x x1 x2 x3 x4 x5 x6

def gchi3_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x3) * dih3_x x1 x2 x3 x4 x5 x6

def gchi4_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x4) * dih4_x x1 x2 x3 x4 x5 x6

def gchi5_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x5) * dih5_x x1 x2 x3 x4 x5 x6

def gchi6_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gchi (holSqrt x6) * dih6_x x1 x2 x3 x4 x5 x6

def ldih_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x1 / 2) * dih_x x1 x2 x3 x4 x5 x6

def ldih2_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x2 / 2) * dih2_x x1 x2 x3 x4 x5 x6

def ldih3_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x3 / 2) * dih3_x x1 x2 x3 x4 x5 x6

def ldih6_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x6 / 2) * dih6_x x1 x2 x3 x4 x5 x6

def matan (x : ℝ) : ℝ :=
  if x = 0 then 1 else if 0 < x then Real.arctan (holSqrt x) / holSqrt x
  else holLog ((1 + holSqrt (-x)) / (1 - holSqrt (-x))) / (2 * holSqrt (-x))

def sol_euler_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let a := holSqrt (x1 * x2 * x3) + holSqrt x1 * (x2 + x3 - x4) / 2 +
    holSqrt x2 * (x1 + x3 - x5) / 2 + holSqrt x3 * (x1 + x2 - x6) / 2
  2 * atn2 (2 * a) (holSqrt (delta_x x1 x2 x3 x4 x5 x6))

def arc_hhn  : ℝ :=
  arclength (2 * h0) (2 * h0) 2

def asn797k (k _x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  k * Real.arcsin (Real.cos (797 / 1000) * Real.sin (Real.pi / k))

def asnFnhk (h k _x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  k * Real.arcsin ((h * sqrt3 / 4 + holSqrt (1 - (h / 2) ^ 2) / 2) *
    Real.sin (Real.pi / k))

def lfun_y1 (y1 _y2 _y3 _y4 _y5 _y6 : ℝ) : ℝ :=
  lfun y1

def acs_sqrt_x1_d4 (x1 _x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  Real.arccos (holSqrt x1 / 4)

def acs_sqrt_x2_d4 (_x1 x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  Real.arccos (holSqrt x2 / 4)

def arclength_x_123 (x1 x2 x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  arclength (holSqrt x1) (holSqrt x2) (holSqrt x3)

def tame_table_d (r s : ℕ) : ℝ :=
  if 3 < r + 2 * s then (103 / 1000) * (2 - (s : ℝ)) +
    (2759 / 10000) * ((r : ℝ) + 2 * (s : ℝ) - 4) else 0

def eta2_126 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (eta_y (holSqrt x1) (holSqrt x2) (holSqrt x6)) ^ 2

def eta2_135 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (eta_y (holSqrt x1) (holSqrt x3) (holSqrt x5)) ^ 2

def eta2_456 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (eta_y (holSqrt x4) (holSqrt x5) (holSqrt x6)) ^ 2

def num1 (e1 e2 e3 a2 b2 c2 : ℝ) : ℝ :=
  -4 * (a2 ^ 2 * e1 + 8 * (b2 - c2) * (e2 - e3) -
    a2 * (16 * e1 + (b2 - 8) * e2 + (c2 - 8) * e3))

def flat_term_x (x : ℝ) : ℝ :=
  flat_term (holSqrt x)

def taum_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhazim_x x1 x2 x3 x4 x5 x6 + rhazim2_x x1 x2 x3 x4 x5 x6 +
    rhazim3_x x1 x2 x3 x4 x5 x6 - (1 + const1) * Real.pi

def eulerA_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  holSqrt x1 * holSqrt x2 * holSqrt x3 + holSqrt x1 * (x2 + x3 - x4) / 2 +
    holSqrt x2 * (x1 + x3 - x5) / 2 + holSqrt x3 * (x1 + x2 - x6) / 2

def delta4_squared_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (delta_x4 x1 x2 x3 x4 x5 x6) ^ 2

def delta4_squared_y  : Scalar6 :=
  y_of_x delta4_squared_x

def x1_delta_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * delta_x x1 x2 x3 x4 x5 x6

def x1_delta_y  : Scalar6 :=
  y_of_x x1_delta_x

def delta_126_x (x3s x4s x5s : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  delta_x x1 x2 x3s x4s x5s x6

def delta_234_x (x1s x5s x6s : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  delta_x x1s x2 x3 x4 x5s x6s

def delta_135_x (x2s x4s x6s : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  delta_x x1 x2s x3 x4s x5 x6s

def delta_sub1_x (x1s : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  delta_x x1s x2 x3 x4 x5 x6

def dihatn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x1 * delta_x x1 x2 x3 x4 x5 x6))

def dih2atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(rotate2 delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x2 * delta_x x1 x2 x3 x4 x5 x6))

def dih3atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(rotate3 delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x3 * delta_x x1 x2 x3 x4 x5 x6))

def dih4atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(rotate4 delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x4 * delta_x x1 x2 x3 x4 x5 x6))

def dih5atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(rotate5 delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x5 * delta_x x1 x2 x3 x4 x5 x6))

def dih6atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 + Real.arctan (-(rotate6 delta_x4 x1 x2 x3 x4 x5 x6) /
    holSqrt (4 * x6 * delta_x x1 x2 x3 x4 x5 x6))

def ldihatn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x1 / 2) * dihatn_x x1 x2 x3 x4 x5 x6

def ldih2atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x2 / 2) * dih2atn_x x1 x2 x3 x4 x5 x6

def ldih3atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x3 / 2) * dih3atn_x x1 x2 x3 x4 x5 x6

def ldih4atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x4 / 2) * dih4atn_x x1 x2 x3 x4 x5 x6

def ldih5atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x5 / 2) * dih5atn_x x1 x2 x3 x4 x5 x6

def ldih6atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x6 / 2) * dih6atn_x x1 x2 x3 x4 x5 x6

def rhazimatn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rho (holSqrt x1) * dihatn_x x1 x2 x3 x4 x5 x6

def rhazim2atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rho (holSqrt x2) * dih2atn_x x1 x2 x3 x4 x5 x6

def rhazim3atn_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rho (holSqrt x3) * dih3atn_x x1 x2 x3 x4 x5 x6

end KeplerMission.Nonlinear

end


/-!
Transparent scalar expressions needed by the finite Flyspeck inequality catalog.
Source: official flyspeck/flyspeck@1ce0353008eba83d3c76ae9a25c3c242e4802d53,
text_formalization/nonlinear/nonlin_def.hl, with each family identified below.
Only function composition and exact real arithmetic are expanded; no source
identity requiring positivity is assumed. HOL signed square roots are preserved.
The function names with `div_sqrtdelta` denote the source expressions on all reals,
not a theorem identifying them with a geometric quotient outside its valid domain.
-/
set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/- nonlin_def.hl:123–206, Euler and dihedral residual expressions. -/
def sol_euler_x_div_sqrtdelta (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let a := holSqrt (x1 * x2 * x3) + holSqrt x1 * (x2 + x3 - x4) / 2 +
    holSqrt x2 * (x1 + x3 - x5) / 2 + holSqrt x3 * (x1 + x2 - x6) / 2
  matan (delta_x x1 x2 x3 x4 x5 x6 / (4 * a ^ 2)) / a

def sol_euler246_x_div_sqrtdelta : Scalar6 := rotate4 sol_euler_x_div_sqrtdelta
def sol_euler345_x_div_sqrtdelta : Scalar6 := rotate5 sol_euler_x_div_sqrtdelta
def sol_euler156_x_div_sqrtdelta : Scalar6 := rotate6 sol_euler_x_div_sqrtdelta

def dih_x_div_sqrtdelta_posbranch (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let d_x4 := delta_x4 x1 x2 x3 x4 x5 x6
  let d := delta_x x1 x2 x3 x4 x5 x6
  (holSqrt (4 * x1) / d_x4) * matan (4 * x1 * d / d_x4 ^ 2)

def ldih_x_div_sqrtdelta_posbranch (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  lfun (holSqrt x1 / 2) * dih_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6

def ldih2_x_div_sqrtdelta_posbranch : Scalar6 := rotate2 ldih_x_div_sqrtdelta_posbranch
def ldih3_x_div_sqrtdelta_posbranch : Scalar6 := rotate3 ldih_x_div_sqrtdelta_posbranch
def ldih5_x_div_sqrtdelta_posbranch : Scalar6 := rotate5 ldih_x_div_sqrtdelta_posbranch
def ldih6_x_div_sqrtdelta_posbranch : Scalar6 := rotate6 ldih_x_div_sqrtdelta_posbranch
def dih4_x_div_sqrtdelta_posbranch : Scalar6 := rotate4 dih_x_div_sqrtdelta_posbranch

def rhazim_x_div_sqrtdelta_posbranch (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rho (holSqrt x1) * dih_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6

def rhazim2_x_div_sqrtdelta_posbranch : Scalar6 := rotate2 rhazim_x_div_sqrtdelta_posbranch
def rhazim3_x_div_sqrtdelta_posbranch : Scalar6 := rotate3 rhazim_x_div_sqrtdelta_posbranch

def tau_residual_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhazim_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6 +
    rhazim2_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6 +
    rhazim3_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6

/- nonlin_def.hl:297–305: squared edge coordinates equal2 in the fixed slots. -/
def mk_126 (f : Scalar6) (x1 x2 _x3 _x4 _x5 x6 : ℝ) : ℝ := f x1 x2 2 2 2 x6
def mk_456 (f : Scalar6) (_x1 _x2 _x3 x4 x5 x6 : ℝ) : ℝ := f 2 2 2 x4 x5 x6
def mk_135 (f : Scalar6) (x1 _x2 x3 _x4 x5 _x6 : ℝ) : ℝ := f x1 2 x3 2 x5 2

/- nonlin_def.hl:376–431. The source marks this corrected gamma2 formula v2. -/
def gamma2_x_div_azim_v2 (m x : ℝ) : ℝ :=
  (8 - x) * holSqrt x / 24 -
    (2 * (2 * mm1 / Real.pi) * (1 - holSqrt x / sqrt8) -
      (8 * mm2 / Real.pi) * m * lfun (holSqrt x / 2))

def gamma2_x1_div_a_v2 (m x1 _x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  gamma2_x_div_azim_v2 m x1

def gamma3f_x_div_sqrtdelta (m4 m5 m6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  1 / 12 -
    ((mk_456 (rotate5 sol_euler_x_div_sqrtdelta) x1 x2 x3 x4 x5 x6 +
      mk_456 (rotate6 sol_euler_x_div_sqrtdelta) x1 x2 x3 x4 x5 x6 +
      mk_456 (rotate4 sol_euler_x_div_sqrtdelta) x1 x2 x3 x4 x5 x6) *
        (2 * mm1 / Real.pi) -
      ((lfun (holSqrt x4 * (1 / 2)) * m4) *
          mk_456 (rotate4 dih_x_div_sqrtdelta_posbranch) x1 x2 x3 x4 x5 x6 +
        (lfun (holSqrt x5 * (1 / 2)) * m5) *
          mk_456 (rotate5 dih_x_div_sqrtdelta_posbranch) x1 x2 x3 x4 x5 x6 +
        (lfun (holSqrt x6 * (1 / 2)) * m6) *
          mk_456 (rotate6 dih_x_div_sqrtdelta_posbranch) x1 x2 x3 x4 x5 x6) *
        (8 * mm2 / Real.pi))

def vol3f_456 (m4 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (mk_456 (rotate5 sol_x) x1 x2 x3 x4 x5 x6 +
    mk_456 (rotate6 sol_x) x1 x2 x3 x4 x5 x6 +
    mk_456 (rotate4 sol_x) x1 x2 x3 x4 x5 x6) * (2 * mm1 / Real.pi) -
    ((lfun (holSqrt x4 * (1 / 2)) * m4) * mk_456 (rotate4 dih_x) x1 x2 x3 x4 x5 x6 +
      lfun (holSqrt x5 * (1 / 2)) * mk_456 (rotate5 dih_x) x1 x2 x3 x4 x5 x6 +
      lfun (holSqrt x6 * (1 / 2)) * mk_456 (rotate6 dih_x) x1 x2 x3 x4 x5 x6) *
      (8 * mm2 / Real.pi)

def gamma3_x (m4 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mk_456 vol_x x1 x2 x3 x4 x5 x6 - vol3f_456 m4 x1 x2 x3 x4 x5 x6

def gamma23_full8_x (m1 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gamma3_x m1 0 0 0 x1 x2 x6 + gamma3_x m1 0 0 0 x1 x3 x5 +
    (dih_x x1 x2 x3 x4 x5 x6 -
      (mk_126 dih_x x1 x2 x3 x4 x5 x6 + mk_135 dih_x x1 x2 x3 x4 x5 x6)) * (8 / 1000)

def gamma23_keep135_x (m1 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  gamma3_x m1 0 0 0 x1 x3 x5 +
    (dih_x x1 x2 x3 x4 x5 x6 - mk_135 dih_x x1 x2 x3 x4 x5 x6) * (8 / 1000)

/- nonlin_def.hl:442–559: the mu/taud and flat-edge residual expressions. -/
def mu_y (y1 y2 y3 : ℝ) : ℝ :=
  12 / 1000 + (7 / 100) * (252 / 100 - y1) +
    (1 / 100) * ((252 / 100) * 2 - y2 - y3)

def mu6_x (x1 x2 x3 _x4 _x5 _x6 : ℝ) : ℝ :=
  12 / 1000 + (7 / 100) * (252 / 100 - holSqrt x1) +
    (1 / 100) * ((252 / 100) * 2 - holSqrt x2 - holSqrt x3)

def taud_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  flat_term_x x1 + holSqrt (delta_x x1 x2 x3 x4 x5 x6) *
    mu_y (holSqrt x1) (holSqrt x2) (holSqrt x3)

def delta_x1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x4 + x2 * x5 - x3 * x5 - x2 * x6 + x3 * x6 +
    x4 * (-x1 + x2 + x3 - x4 + x5 + x6)

def dnum1 (e1 e2 e3 x4 x5 x6 : ℝ) : ℝ :=
  (16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3

def taud_D1_num_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let d := delta_x x1 x2 x3 x4 x5 x6
  let dp := delta_x1 x1 x2 x3 x4 x5 x6 * 2 * holSqrt x1
  let mu := mu6_x x1 x2 x3 x4 x5 x6
  let mup : ℝ := -(7 / 100)
  let ftp := sol0 / (52 / 100)
  mup * d + (1 / 2) * mu * dp + ftp * holSqrt d

def taud_D2_num_x (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let d := delta_x x1 x2 x3 x4 x5 x6
  let dp := delta_x1 x1 x2 x3 x4 x5 x6 * 2 * holSqrt x1
  let dpp := -8 * x1 * x4 + delta_x1 x1 x2 x3 x4 x5 x6 * 2
  let mu := mu6_x x1 x2 x3 x4 x5 x6
  let mup : ℝ := -(7 / 100)
  mup * d * dp - (1 / 4) * mu * (dp * dp) + (1 / 2) * mu * d * dpp

def edge2_flatD_x1 (d x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  quadratic_root_plus (abc_of_quadratic (fun x1 ↦ d - delta_x x1 x2 x3 x4 x5 x6))

def edge2_126_x (d x4 x5 x1 x2 _x3 _x4 _x5 x6 : ℝ) : ℝ :=
  edge2_flatD_x1 d x1 x2 x6 x4 x5

def edge2_135_x (d x4 x6 x1 _x2 x3 _x4 x5 _x6 : ℝ) : ℝ :=
  edge2_flatD_x1 d x1 x3 x5 x4 x6

def edge2_234_x (d x5 x6 _x1 x2 x3 x4 _x5 _x6 : ℝ) : ℝ :=
  edge2_flatD_x1 d x2 x3 x4 x5 x6

def flat_term2_126_x (d x4 x5 x1 x2 x3 x4' x5' x6 : ℝ) : ℝ :=
  flat_term_x (edge2_126_x d x4 x5 x1 x2 x3 x4' x5' x6)

def flat_term2_135_x (d x4 x6 x1 x2 x3 x4' x5 x6' : ℝ) : ℝ :=
  flat_term_x (edge2_135_x d x4 x6 x1 x2 x3 x4' x5 x6')

def flat_term2_234_x (d x5 x6 x1 x2 x3 x4 x5' x6' : ℝ) : ℝ :=
  flat_term_x (edge2_234_x d x5 x6 x1 x2 x3 x4 x5' x6')

def mud_135_x_v1 (y2 y4 y6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu_y y2 (holSqrt x1) (holSqrt x3) *
    holSqrt (delta_135_x (y2 * y2) (y4 * y4) (y6 * y6) x1 x2 x3 x4 x5 x6)

def mud_126_x_v1 (y3 y4 y5 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu_y y3 (holSqrt x1) (holSqrt x2) *
    holSqrt (delta_126_x (y3 * y3) (y4 * y4) (y5 * y5) x1 x2 x3 x4 x5 x6)

def mud_234_x_v1 (y1 y5 y6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu_y y1 (holSqrt x2) (holSqrt x3) *
    holSqrt (delta_234_x (y1 * y1) (y5 * y5) (y6 * y6) x1 x2 x3 x4 x5 x6)

/- Preserve mu6_x (squared constant), not mu_y with an unstated nonnegative parameter. -/
def mudLs_234_x (d1s d2s y1 y5 y6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu6_x (y1 * y1) x2 x3 0 0 0 *
    ((1 / (d1s + d2s)) *
      (delta_234_x (y1 * y1) (y5 * y5) (y6 * y6) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

def mudLs_126_x (d1s d2s y3 y4 y5 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu6_x (y3 * y3) x1 x2 0 0 0 *
    ((1 / (d1s + d2s)) *
      (delta_126_x (y3 * y3) (y4 * y4) (y5 * y5) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

def mudLs_135_x (d1s d2s y2 y4 y6 x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  mu6_x (y2 * y2) x1 x3 0 0 0 *
    ((1 / (d1s + d2s)) *
      (delta_135_x (y2 * y2) (y4 * y4) (y6 * y6) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)

/- Exact polynomial from leg/cayleyR_def.hl:33–61. -/
def cayleyR (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℝ) : ℝ :=
- (x14*x14*x23*x23) + 2 *x14*x15*x23*x23 - x15*x15*x23*x23 + 2 *x13*x14*x23*x24 - 2 *x13*x15*x23*x24 - 2 *x14*x15*x23*x24 + 
   2 *x15*x15*x23*x24 - x13*x13*x24*x24 + 2 *x13*x15*x24*x24 - x15*x15*x24*x24 - 2 *x13*x14*x23*x25 + 
   2 *x14*x14*x23*x25 + 2 *x13*x15*x23*x25 - 2 *x14*x15*x23*x25 + 2 *x13*x13*x24*x25 - 2 *x13*x14*x24*x25 - 2 *x13*x15*x24*x25 + 
   2 *x14*x15*x24*x25 - x13*x13*x25*x25 + 2 *x13*x14*x25*x25 - x14*x14*x25*x25 + 2 *x12*x14*x23*x34 - 2 *x12*x15*x23*x34 - 
   2 *x14*x15*x23*x34 + 2 *x15*x15*x23*x34 + 2 *x12*x13*x24*x34 - 2 *x12*x15*x24*x34 - 2 *x13*x15*x24*x34 + 2 *x15*x15*x24*x34 + 
   4 *x15*x23*x24*x34 - 2 *x12*x13*x25*x34 - 2 *x12*x14*x25*x34 + 4 *x13*x14*x25*x34 + 4 *x12*x15*x25*x34 - 2 *x13*x15*x25*x34 - 2 *x14*x15*x25*x34 - 
   2 *x14*x23*x25*x34 - 2 *x15*x23*x25*x34 - 2 *x13*x24*x25*x34 - 2 *x15*x24*x25*x34 + 2 *x13*x25*x25*x34 + 2 *x14*x25*x25*x34 - 
   x12*x12*x34*x34 + 2 *x12*x15*x34*x34 - x15*x15*x34*x34 + 2 *x12*x25*x34*x34 + 2 *x15*x25*x34*x34 - 
   x25*x25*x34*x34 - 2 *x12*x14*x23*x35 + 2 *x14*x14*x23*x35 + 2 *x12*x15*x23*x35 - 2 *x14*x15*x23*x35 - 2 *x12*x13*x24*x35 + 
   4 *x12*x14*x24*x35 - 2 *x13*x14*x24*x35 - 2 *x12*x15*x24*x35 + 4 *x13*x15*x24*x35 - 2 *x14*x15*x24*x35 - 2 *x14*x23*x24*x35 - 2 *x15*x23*x24*x35 + 
   2 *x13*x24*x24*x35 + 2 *x15*x24*x24*x35 + 2 *x12*x13*x25*x35 - 2 *x12*x14*x25*x35 - 2 *x13*x14*x25*x35 + 2 *x14*x14*x25*x35 + 
   4 *x14*x23*x25*x35 - 2 *x13*x24*x25*x35 - 2 *x14*x24*x25*x35 + 2 *x12*x12*x34*x35 - 2 *x12*x14*x34*x35 - 2 *x12*x15*x34*x35 + 
   2 *x14*x15*x34*x35 - 2 *x12*x24*x34*x35 - 2 *x15*x24*x34*x35 - 2 *x12*x25*x34*x35 - 2 *x14*x25*x34*x35 + 2 *x24*x25*x34*x35 - 
   x12*x12*x35*x35 + 2 *x12*x14*x35*x35 - x14*x14*x35*x35 + 2 *x12*x24*x35*x35 + 2 *x14*x24*x35*x35 - 
   x24*x24*x35*x35 + 4 *x12*x13*x23*x45 - 2 *x12*x14*x23*x45 - 2 *x13*x14*x23*x45 - 2 *x12*x15*x23*x45 - 2 *x13*x15*x23*x45 + 
   4 *x14*x15*x23*x45 + 2 *x14*x23*x23*x45 + 2 *x15*x23*x23*x45 - 2 *x12*x13*x24*x45 + 2 *x13*x13*x24*x45 + 2 *x12*x15*x24*x45 - 
   2 *x13*x15*x24*x45 - 2 *x13*x23*x24*x45 - 2 *x15*x23*x24*x45 - 2 *x12*x13*x25*x45 + 2 *x13*x13*x25*x45 + 2 *x12*x14*x25*x45 - 
   2 *x13*x14*x25*x45 - 2 *x13*x23*x25*x45 - 2 *x14*x23*x25*x45 + 4 *x13*x24*x25*x45 + 2 *x12*x12*x34*x45 - 2 *x12*x13*x34*x45 - 
   2 *x12*x15*x34*x45 + 2 *x13*x15*x34*x45 - 2 *x12*x23*x34*x45 - 2 *x15*x23*x34*x45 - 2 *x12*x25*x34*x45 - 2 *x13*x25*x34*x45 + 2 *x23*x25*x34*x45 + 
   2 *x12*x12*x35*x45 - 2 *x12*x13*x35*x45 - 2 *x12*x14*x35*x45 + 2 *x13*x14*x35*x45 - 2 *x12*x23*x35*x45 - 2 *x14*x23*x35*x45 - 
   2 *x12*x24*x35*x45 - 2 *x13*x24*x35*x45 + 2 *x23*x24*x35*x45 + 4 *x12*x34*x35*x45 - x12*x12*x45*x45 + 2 *x12*x13*x45*x45 - 
   x13*x13*x45*x45 + 2 *x12*x23*x45*x45 + 2 *x13*x23*x45*x45 - x23*x23*x45*x45

/- Exact polynomial from leg/collect_geom.hl:164–213. -/
def cayleytr (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℝ) : ℝ :=
2 * x23 * x25 * x34 +
      2 * x23 * x24 * x35 +
      - 1 * x23 ^ 2 * x45 +
      - 2 * x15 * x23 * x34 +
      - 2 * x15 * x23 * x24 +
      2 * x15 * x23 ^ 2 +
      - 2 * x14 * x23 * x35 +
      - 2 * x14 * x23 * x25 +
      2 * x14 * x23 ^ 2 +
      4 * x14 * x15 * x23 +
      - 2 * x13 * x25 * x34 +
      - 2 * x13 * x24 * x35 +
      4 * x13 * x24 * x25 +
      2 * x13 * x23 * x45 +
      - 2 * x13 * x23 * x25 +
      - 2 * x13 * x23 * x24 +
      2 * x13 * x15 * x34 +
      - 2 * x13 * x15 * x24 +
      - 2 * x13 * x15 * x23 +
      2 * x13 * x14 * x35 +
      - 2 * x13 * x14 * x25 +
      - 2 * x13 * x14 * x23 +
      - 1 * x13 ^ 2 * x45 +
      2 * x13 ^ 2 * x25 +
      2 * x13 ^ 2 * x24 +
      4 * x12 * x34 * x35 +
      - 2 * x12 * x25 * x34 +
      - 2 * x12 * x24 * x35 +
      2 * x12 * x23 * x45 +
      - 2 * x12 * x23 * x35 +
      - 2 * x12 * x23 * x34 +
   - 2 * x12 * x15 * x34 +
      2 * x12 * x15 * x24 +
      - 2 * x12 * x15 * x23 +
      - 2 * x12 * x14 * x35 +
      2 * x12 * x14 * x25 +
      - 2 * x12 * x14 * x23 +
      2 * x12 * x13 * x45 +
      - 2 * x12 * x13 * x35 +
      - 2 * x12 * x13 * x34 +
      - 2 * x12 * x13 * x25 +
      - 2 * x12 * x13 * x24 +
      4 * x12 * x13 * x23 +
      - 1 * x12 ^ 2 * x45 +
      2 * x12 ^ 2 * x35 +
      2 * x12 ^ 2 * x34

end KeplerMission.Nonlinear

end


/-!
# Nonlinear problems and certificate contracts

Real semantics and certificate-data interfaces for the nonlinear branch of Flyspeck.
Source: Hales et al. (2017), Sections 5–6; Solovyev–Hales (2013), Sections 2–3.
A checker is supplied separately from its soundness theorem and from successful certificates.
No particular nonlinear inequality is assumed in these definitions.
-/

set_option autoImplicit false

namespace KeplerMission.Nonlinear

/-- A source obligation, with every real variable quantified in `Valid`.
The source's closed interval constraints form `domain`; disjunctions are preserved in `conclusion`. -/
structure Problem where
  arity : ℕ
  domain : (Fin arity → ℝ) → Prop
  conclusion : (Fin arity → ℝ) → Prop

/-- Mathematical validity, independent of a numerical algorithm or certificate. -/
def Problem.Valid (p : Problem) : Prop :=
  ∀ x : Fin p.arity → ℝ, p.domain x → p.conclusion x

mutual
  /-- Exact expression syntax. Rational constants have no floating-point interpretation.
  The square-root constructor uses HOL Light's signed totalization in `Expr.eval`.
  Source functions can be reduced to this syntax only with an explicit semantic bridge. -/
  inductive Expr (n : ℕ) where
    | rational : ℚ → Expr n
    | variable : Fin n → Expr n
    | pi : Expr n
    | add : Expr n → Expr n → Expr n
    | sub : Expr n → Expr n → Expr n
    | mul : Expr n → Expr n → Expr n
    | div : Expr n → Expr n → Expr n
    | neg : Expr n → Expr n
    | pow : Expr n → ℕ → Expr n
    | sqrt : Expr n → Expr n
    | arctan : Expr n → Expr n
    | sin : Expr n → Expr n
    | cos : Expr n → Expr n
    | arcsin : Expr n → Expr n
    | arccos : Expr n → Expr n
    | log : Expr n → Expr n
    | hminus : Expr n
    | abs : Expr n → Expr n
    | ite : Formula n → Expr n → Expr n → Expr n

  /-- Boolean combinations retain strict/non-strict comparisons and source disjunctions. -/
  inductive Formula (n : ℕ) where
    | le : Expr n → Expr n → Formula n
    | lt : Expr n → Expr n → Formula n
    | eq : Expr n → Expr n → Formula n
    | negation : Formula n → Formula n
    | conjunction : Formula n → Formula n → Formula n
    | disjunction : Formula n → Formula n → Formula n
    | implication : Formula n → Formula n → Formula n
end

mutual
  noncomputable def Expr.eval {n : ℕ} (x : Fin n → ℝ) : Expr n → ℝ
    | .rational q => q
    | .variable i => x i
    | .pi => Real.pi
    | .add a b => a.eval x + b.eval x
    | .sub a b => a.eval x - b.eval x
    | .mul a b => a.eval x * b.eval x
    | .div a b => a.eval x / b.eval x
    | .neg a => -a.eval x
    | .pow a k => a.eval x ^ k
    | .sqrt a => if 0 ≤ a.eval x then Real.sqrt (a.eval x) else -Real.sqrt (-a.eval x)
    | .arctan a => Real.arctan (a.eval x)
    | .sin a => Real.sin (a.eval x)
    | .cos a => Real.cos (a.eval x)
    | .arcsin a => Real.arcsin (a.eval x)
    | .arccos a => Real.arccos (a.eval x)
    | .log a => holLog (a.eval x)
    | .hminus => KeplerMission.Nonlinear.hminus
    | .abs a => |a.eval x|
    | .ite p a b => @ite ℝ (p.eval x) (Classical.propDecidable _) (a.eval x) (b.eval x)

  noncomputable def Formula.eval {n : ℕ} (x : Fin n → ℝ) : Formula n → Prop
    | .le a b => a.eval x ≤ b.eval x
    | .lt a b => a.eval x < b.eval x
    | .eq a b => a.eval x = b.eval x
    | .negation p => ¬p.eval x
    | .conjunction p q => p.eval x ∧ q.eval x
    | .disjunction p q => p.eval x ∨ q.eval x
    | .implication p q => p.eval x → q.eval x
end

/-- Exact rational endpoints. Empty intervals are allowed and retain their usual semantics. -/
structure Interval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

def Interval.Contains (i : Interval) (x : ℝ) : Prop :=
  (i.lower : ℝ) ≤ x ∧ x ≤ (i.upper : ℝ)

abbrev Box (n : ℕ) := Fin n → Interval

def Box.Contains {n : ℕ} (b : Box n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (b i).Contains (x i)

structure EncodedProblem (n : ℕ) where
  box : Box n
  domain : Formula n
  formula : Formula n

def EncodedProblem.Valid {n : ℕ} (p : EncodedProblem n) : Prop :=
  ∀ x, p.box.Contains x → p.domain.eval x → p.formula.eval x

/-- A pointwise, rather than merely propositional, bridge from expression syntax to the
exact source domain and conclusion. It is an obligation, not an unchecked converter. -/
def EncodedProblem.Encodes (p : Problem) (e : EncodedProblem p.arity) : Prop :=
  (∀ x, p.domain x ↔ e.box.Contains x ∧ e.domain.eval x) ∧
  (∀ x, p.domain x → (p.conclusion x ↔ e.formula.eval x))

/-- Proposed rational enclosure for an expression over the current box. -/
structure Enclosure (n : ℕ) where
  expression : Expr n
  interval : Interval

/-- Data needed for a second-order Taylor enclosure. Bounds are checked, never assumed.
`center` is rational; the value, gradient and Hessian enclosures use exact endpoints. -/
structure TaylorData (n : ℕ) where
  expression : Expr n
  center : Fin n → ℚ
  value : Interval
  gradient : Fin n → Interval
  hessian : Fin n → Fin n → Interval

/-- Search output. Splits must cover the parent box. A monotonicity reduction needs verified
sign bounds for the specified partial derivative. Leaves retain the selected disjunct. -/
inductive Certificate (n : ℕ) where
  | intervalLeaf : List (Enclosure n) → ℕ → Certificate n
  | taylorLeaf : List (TaylorData n) → ℕ → Certificate n
  | split : Fin n → ℚ → Certificate n → Certificate n → Certificate n
  | monotone : Fin n → Bool → List (Enclosure n) → Certificate n → Certificate n

/-- An implementation to be supplied by the mission. Giving this function does not prove
soundness or exhibit an accepted certificate for any source obligation. -/
abbrev Checker := (n : ℕ) → EncodedProblem n → Certificate n → Bool

/-- Checker correctness is an ordinary Lean theorem about real denotations. -/
def Checker.Sound (check : Checker) : Prop :=
  ∀ n p cert, check n p cert = true → p.Valid

/-- Acceptance of one explicit data object. -/
def Checker.Accepts (check : Checker) {n : ℕ}
    (p : EncodedProblem n) (cert : Certificate n) : Prop := check n p cert = true

/-- The data-completeness obligation is separate from generic checker soundness. Each source
problem needs its own pointwise encoding bridge and a successfully checked certificate. -/
def CatalogCertified (catalog : List Problem) (check : Checker) : Prop :=
  ∀ p ∈ catalog, ∃ e : EncodedProblem p.arity, ∃ cert : Certificate p.arity,
    e.Encodes p ∧ check.Accepts e cert

/-- Generic integration contract. Its inputs do not include any source-specific inequality. -/
def CatalogCertificationSoundness : Prop :=
  ∀ (catalog : List Problem) (check : Checker),
    check.Sound → CatalogCertified catalog check → ∀ p ∈ catalog, p.Valid

/-- Generic kernel-checked transfer. This proves no catalog inequality: soundness, exact
encoding, and successful certificate checks are all explicit inputs. -/
theorem catalog_valid_of_certified (catalog : List Problem) (check : Checker)
    (hsound : check.Sound) (hcert : CatalogCertified catalog check) :
    ∀ p ∈ catalog, p.Valid := by
  intro p hp x hx
  obtain ⟨e, cert, he, hc⟩ := hcert p hp
  have hd := (he.1 x).mp hx
  have hf := hsound p.arity e cert hc x hd.1 hd.2
  exact (he.2 x hx).mpr hf

end KeplerMission.Nonlinear

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear
/-- Closed constraints from Sphere.ineq: each triple is (lower, value, upper). -/
def inClosedIntervals (bounds : List (ℝ × ℝ × ℝ)) : Prop :=
  ∀ t ∈ bounds, t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2

/-- Source: ineq.hl, domain definition `dart_std3`. -/
def dart_std3 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((2 : ℝ) , (y4 , (63 / 25 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dartX`. -/
def dartX (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dartY`. -/
def dartY (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart4_diag3`. -/
def dart4_diag3 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((3 : ℝ) , (y4 , (3 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_flat`. -/
def apex_flat (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_A`. -/
def apex_A (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((2 : ℝ) , (y4 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y5 , sqrt8)), ((63 / 25 : ℝ) , (y6 , sqrt8))]

/-- Source: ineq.hl, domain definition `dart_std3_small`. -/
def dart_std3_small (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((2 : ℝ) , (y4 , (9 / 4 : ℝ))), ((2 : ℝ) , (y5 , (9 / 4 : ℝ))), ((2 : ℝ) , (y6 , (9 / 4 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_std3_big`. -/
def dart_std3_big :=
  dart_std3

/-- Source: ineq.hl, domain definition `apex_sup_flat`. -/
def apex_sup_flat (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , (3 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_std3_mini`. -/
def dart_std3_mini (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (9 / 4 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_flat_hll`. -/
def apex_flat_hll (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (109 / 50 : ℝ))), ((2 : ℝ) , (y3 , (109 / 50 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_std3_big_200_218`. -/
def dart_std3_big_200_218 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (109 / 50 : ℝ))), ((2 : ℝ) , (y2 , (109 / 50 : ℝ))), ((2 : ℝ) , (y3 , (109 / 50 : ℝ))), ((2 : ℝ) , (y4 , (63 / 25 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_std3_hll`. -/
def apex_std3_hll (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_std3_small_hll`. -/
def apex_std3_small_hll (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (9 / 4 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_mll_w`. -/
def dart_mll_w (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (59 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), ((9 / 4 : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_mll_n`. -/
def dart_mll_n (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (59 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_Hll_n`. -/
def dart_Hll_n (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((59 / 25 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (9 / 4 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_Hll_w`. -/
def dart_Hll_w (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((59 / 25 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), ((9 / 4 : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `dart_std3_lw`. -/
def dart_std3_lw (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((9 / 4 : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_flat_l`. -/
def apex_flat_l (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_flat_h`. -/
def apex_flat_h (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((109 / 50 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_std3_lll_xww`. -/
def apex_std3_lll_xww (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(((2 : ℕ) : ℝ) , (y1 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), ((9 / 4 : ℝ) , (y5 , (63 / 25 : ℝ))), ((9 / 4 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_std3_lll_wxx`. -/
def apex_std3_lll_wxx (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(((2 : ℕ) : ℝ) , (y1 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (109 / 50 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (109 / 50 : ℝ))), ((9 / 4 : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apex_std3_lhh`. -/
def apex_std3_lhh (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [(((2 : ℕ) : ℝ) , (y1 , (109 / 50 : ℝ))), ((109 / 50 : ℝ) , (y2 , (63 / 25 : ℝ))), ((109 / 50 : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apexffA`. -/
def apexffA (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y6 , sqrt8))]

/-- Source: ineq.hl, domain definition `apexfA`. -/
def apexfA (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , sqrt8)), ((63 / 25 : ℝ) , (y5 , sqrt8)), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apexf4`. -/
def apexf4 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y6 , sqrt8))]

/-- Source: ineq.hl, domain definition `apexff4`. -/
def apexff4 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , sqrt8)), ((63 / 25 : ℝ) , (y5 , sqrt8)), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

/-- Source: ineq.hl, domain definition `apexf5`. -/
def apexf5 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), ((2 : ℝ) , (y5 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y6 , sqrt8))]

/-- Source: ineq.hl, domain definition `apexff5`. -/
def apexff5 (y1 y2 y3 y4 y5 y6 : ℝ) : List (ℝ × ℝ × ℝ) :=
  [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y5 , sqrt8)), ((2 : ℝ) , (y6 , (63 / 25 : ℝ)))]

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `TSKAJXY-TADIAMB`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:127. -/
def problem000 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), ((((2 : ℕ) : ℝ) * hplus) , (y2 , sqrt8)), ((2 : ℝ) , (y3 , sqrt8)), ((2 : ℝ) , (y4 , sqrt8)), ((2 : ℝ) , (y5 , sqrt8)), ((2 : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))

/-- `TSKAJXY-RIBCYXU sharp`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:165. -/
def problem001 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2 : ℝ) , (y1 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y2 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y3 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y4 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y5 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y6 , (2001 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) >= ((0 : ℕ) : ℝ))

/-- `TSKAJXY-RIBCYXU sym`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:183. -/
def problem002 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2001 / 1000 : ℝ) , (y1 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > ((0 : ℕ) : ℝ)) ∨ ((y1 < y2) ∨ ((y1 < y3) ∨ ((y1 < y4) ∨ ((y1 < y5) ∨ ((y1 < y6) ∨ ((y2 < y3) ∨ ((y2 < y5) ∨ (y2 < y6)))))))))

/-- `TSKAJXY-IYOUOBF sym`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:223. -/
def problem003 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), ((2001 / 1000 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) >= ((0 : ℕ) : ℝ)) ∨ ((y2 < y3) ∨ ((y2 < y5) ∨ (y2 < y6))))

/-- `TSKAJXY-IYOUOBF sharp v2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:242. -/
def problem004 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), ((2 : ℝ) , (y2 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y3 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y5 , (2001 / 1000 : ℝ))), ((2 : ℝ) , (y6 , (2001 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) >= ((0 : ℕ) : ℝ))

/-- `TSKAJXY-WKGUESB sym`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:281. -/
def problem005 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), ((201 / 100 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), ((2 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > ((0 : ℕ) : ℝ)) ∨ ((y2 < y3) ∨ ((y2 < y5) ∨ ((y2 < y6) ∨ (y1 < y4)))))

/-- `TSKAJXY-XLLIPLS`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:304. -/
def problem006 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), ((2 : ℝ) , (y2 , (201 / 100 : ℝ))), ((2 : ℝ) , (y3 , (201 / 100 : ℝ))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , (14 / 5 : ℝ))), ((2 : ℝ) , (y5 , (201 / 100 : ℝ))), ((2 : ℝ) , (y6 , (201 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > ((0 : ℕ) : ℝ))

/-- `TSKAJXY-eulerA`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:324. -/
def problem007 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((14 / 5 : ℝ) ^ 2) , (x1 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x2 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x3 , ((201 / 100 : ℝ) ^ 2))), (((14 / 5 : ℝ) ^ 2) , (x4 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x5 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x6 , ((201 / 100 : ℝ) ^ 2)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((0 : ℕ) : ℝ) < ((((((eulerA_x x1) x2) x3) x4) x5) x6))

/-- `TSKAJXY-delta_x4`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:341. -/
def problem008 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x2 , ((201 / 100 : ℝ) ^ 2))), (((14 / 5 : ℝ) ^ 2) , (x3 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x4 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x5 , ((201 / 100 : ℝ) ^ 2))), (((14 / 5 : ℝ) ^ 2) , (x6 , ((8 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((0 : ℕ) : ℝ) < ((((((delta_x4 x1) x2) x3) x4) x5) x6))

/-- `TSKAJXY-GXSABWC DIV`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:359. -/
def problem009 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((14 / 5 : ℝ) ^ 2) , (x1 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x2 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x3 , ((201 / 100 : ℝ) ^ 2))), (((14 / 5 : ℝ) ^ 2) , (x4 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x5 , ((201 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x6 , ((201 / 100 : ℝ) ^ 2)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((((1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) - (((((2 : ℕ) : ℝ) * (mm1 / Real.pi)) * (((((((sol_euler_x_div_sqrtdelta x1) x2) x3) x4) x5) x6) + (((((((sol_euler345_x_div_sqrtdelta x1) x2) x3) x4) x5) x6) + (((((((sol_euler156_x_div_sqrtdelta x1) x2) x3) x4) x5) x6) + ((((((sol_euler246_x_div_sqrtdelta x1) x2) x3) x4) x5) x6))))) - ((((8 : ℕ) : ℝ) * (mm2 / Real.pi)) * (((((((ldih2_x_div_sqrtdelta_posbranch x1) x2) x3) x4) x5) x6) + (((((((ldih3_x_div_sqrtdelta_posbranch x1) x2) x3) x4) x5) x6) + (((((((ldih5_x_div_sqrtdelta_posbranch x1) x2) x3) x4) x5) x6) + ((((((ldih6_x_div_sqrtdelta_posbranch x1) x2) x3) x4) x5) x6))))))) >= ((0 : ℕ) : ℝ)) ∨ (((((((delta_x x1) x2) x3) x4) x5) x6) < ((0 : ℕ) : ℝ)))

/-- `ZTGIJCF0`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:447. -/
def problem010 : Problem where
  arity := 1
  domain := fun x ↦
    let dummy := x 0;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (dummy , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let dummy := x 0;
    (((((5 : ℕ) : ℝ) * a_spine5) + (b_spine5 * (((2 : ℕ) : ℝ) * Real.pi))) > ((0 : ℕ) : ℝ))

/-- `ZTGIJCF4 0 0 0 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem011 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 0 0 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem012 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 0 1 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem013 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 0 1 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem014 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 1 0 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem015 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + (((1 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 1 0 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem016 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 1 1 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem017 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 0 1 1 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem018 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((4 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 0 0 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem019 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 0 0 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem020 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 0 1 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem021 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 0 1 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem022 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((4 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 1 0 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem023 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 1 0 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem024 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((4 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 1 1 0 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem025 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((4 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `ZTGIJCF4 1 1 1 1 1821661595`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:495. -/
def problem026 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((5 : ℕ) : ℝ)) + (((0 : ℕ) : ℝ) * beta_bump_lb)) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `MKFKQWU`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:503. -/
def problem027 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hminus) , (y2 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))

/-- `MKFKQWU halfwt`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:524. -/
def problem028 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hplus) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))

/-- `GLFVCVK4 2477216213`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:560. -/
def problem029 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > ((0 : ℕ) : ℝ)) ∨ ((((((((norm2hh y1) y2) y3) y4) y5) y6) < ((hplus - hminus) ^ 2)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))))

/-- `GLFVCVK4a 8328676778`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:587. -/
def problem030 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) > ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `GLFVCVK4 2477216213 y4crit`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:624. -/
def problem031 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hminus) , (y2 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))))

/-- `GLFVCVK4 2477216213 y4supercrit`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:650. -/
def problem032 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))))

/-- `GLFVCVK4 2477216213 y4subcrit`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:676. -/
def problem033 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hminus) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ))))

/-- `BIXPCGW 6652007036 a2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:702. -/
def problem034 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (14 / 5 : ℝ))

/-- `BIXPCGW 7080972881 a2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:722. -/
def problem035 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hminus) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (23 / 10 : ℝ))

/-- `BIXPCGW 1738910218 a2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:740. -/
def problem036 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (23 / 10 : ℝ))

/-- `BIXPCGW b`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:759. -/
def problem037 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta4_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ ((((((((delta_y y1) y2) y3) y4) y5) y6) > ((60 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `BIXPCGW 7274157868 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:777. -/
def problem038 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > (57 / 10000 : ℝ)) ∨ (((((((dih_y y1) y2) y3) y4) y5) y6) < (23 / 10 : ℝ)))

/-- `QITNPEA 9939613598`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:799. -/
def problem039 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) - (457511 / 100000000 : ℝ)) - ((609451 / 100000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) > (0 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `QITNPEA1 1 0 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem040 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA1 1 1 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem041 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((3 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA1 1 2 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem042 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y3 , (((2 : ℕ) : ℝ) * hplus))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA1 2 0 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem043 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA1 2 1 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem044 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA1 2 2 9063653052 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:860. -/
def problem045 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hplus) , (y3 , sqrt8)), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) > (57 / 10000 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `QITNPEA 2134082733`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:865. -/
def problem046 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((beta_bump_lb - (213849 / 1000000 : ℝ)) + ((59741 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)))) > (0 : ℝ)) ∨ ((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)))

/-- `FHBVYXZv2 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:889. -/
def problem047 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > (57 / 10000 : ℝ)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y3) y5) ^ 2) < ((67 / 50 : ℝ) ^ 2))))

/-- `FHBVYXZ a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:915. -/
def problem048 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2))))

/-- `FHBVYXZ b`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:943. -/
def problem049 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) + (((((gamma3f y1) y2) y6) sqrt2) lmfun)) > ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2))))

/-- `FWGKMBZ`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:968. -/
def problem050 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x delta_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `BIXPCGW 9455898160`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:986. -/
def problem051 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) > (-(569 / 100000 : ℝ)))

/-- `QITNPEA 5653753305`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1005. -/
def problem052 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) + ((659 / 10000 : ℝ) - ((21 / 500 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)))) > (0 : ℝ))

/-- `QITNPEA 6206775865`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1024. -/
def problem053 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) + ((35713 / 2500000 : ℝ) - ((609451 / 100000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)))) > (0 : ℝ))

/-- `QITNPEA 5814748276`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1042. -/
def problem054 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) - (63781 / 50000000 : ℝ)) + ((522841 / 100000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) > (0 : ℝ))

/-- `QITNPEA 3848804089`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1060. -/
def problem055 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) - (161517 / 1000000 : ℝ)) + ((59741 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) > (0 : ℝ))

/-- `QITNPEA  5400790175 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1104. -/
def problem056 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + beta_bump_lb) > (57 / 10000 : ℝ)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2))))

/-- `QITNPEA  5400790175 b`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1122. -/
def problem057 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + (beta_bump_lb + (((((gamma3f y1) y2) y6) sqrt2) lmfun))) > (57 / 10000 : ℝ)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2))))

/-- `TEWNSCJ`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1147. -/
def problem058 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (gamma23_full8_x (h0cut y1))) y1) y2) y3) y4) y5) y6) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) < ((2 : ℕ) : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ (((((eta_y y1) y3) y5) ^ 2) > ((67 / 50 : ℝ) ^ 2)))))

/-- `PEMKWKU`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1170. -/
def problem059 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (gamma23_keep135_x (h0cut y1))) y1) y2) y3) y4) y5) y6) > (a_spine5 + (b_spine5 * ((((((dih_y y1) y2) y3) y4) y5) y6)))) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) < ((2 : ℕ) : ℝ)) ∨ ((((((((dih_y y1) y2) y3) y4) y5) y6) > (537 / 500 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) > ((2 : ℕ) : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) < ((67 / 50 : ℝ) ^ 2)) ∨ (((((eta_y y1) y3) y5) ^ 2) > ((67 / 50 : ℝ) ^ 2)))))))

/-- `QITNPEAv2 4003532128`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1194. -/
def problem060 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ ((((((eta_y y1) y3) y5) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) < ((2 : ℕ) : ℝ)) ∨ ((y2 < y3) ∨ ((y2 < y5) ∨ ((y2 < y6) ∨ ((((((((((y_of_x (gamma23_full8_x (h0cut y1))) y1) y2) y3) y4) y5) y6) - (457511 / 100000000 : ℝ)) - ((609451 / 100000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) > (0 : ℝ))))))))

/-- `QITNPEA 3725403817`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1222. -/
def problem061 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), ((2 : ℝ) , (y4 , (21 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (39 / 25 : ℝ))

/-- `TXQTPVC`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1242. -/
def problem062 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (gamma23_full8_x (h0cut y1))) y1) y2) y3) y4) y5) y6) > (((3 : ℕ) : ℝ) * (57 / 10000 : ℝ))) ∨ (((((((((y_of_x rad2_x) y1) y2) y3) y4) y5) y6) < ((2 : ℕ) : ℝ)) ∨ ((((((((dih_y y1) y2) y3) y4) y5) y6) > (2089 / 1000 : ℝ)) ∨ ((((((((dih_y y1) y2) y3) y4) y5) y6) < (973 / 500 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ (((((eta_y y1) y3) y5) ^ 2) > ((67 / 50 : ℝ) ^ 2)))))))

/-- `IXPOTPA`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1266. -/
def problem063 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * hminus))), (sqrt8 , (y4 , (((4 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (307 / 100 : ℝ); (let tan2upper := (129 / 20 : ℝ); ((((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta4_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) > (tan2upper * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ ((((((eta_y y1) y2) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ ((((((eta_y y1) y3) y5) ^ 2) > ((67 / 50 : ℝ) ^ 2)) ∨ ((((((((y_of_x (gamma23_full8_x (h0cut y1))) y1) y2) y3) y4) y5) y6) > (((3 : ℕ) : ℝ) * (57 / 10000 : ℝ)))))))))))

/-- `QITNPEA 4003532128 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1291. -/
def problem064 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (sqrt2 , (y3 , sqrt2)), (sqrt2 , (y4 , sqrt2)), (sqrt2 , (y5 , sqrt2)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta4_y y1) y2) y3) y4) y5) y6) > ((25 : ℕ) : ℝ)) ∨ ((((((((delta_y y1) y2) y3) y4) y5) y6) > (7 / 50 : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `RQWUDDU`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1333. -/
def problem065 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih_y y1) y2) y3) y4) y5) y6) > (19 / 25 : ℝ)) ∨ ((((((eta_y y1) y2) y6) ^ 2) > ((2 : ℕ) : ℝ)) ∨ (((((eta_y y1) y3) y5) ^ 2) > ((2 : ℕ) : ℝ))))

/-- `GCKBQEA`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1353. -/
def problem066 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hminus) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y2 , sqrt8)), (((2 : ℕ) : ℝ) , (y3 , sqrt8)), (((2 : ℕ) : ℝ) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) > (303 / 500 : ℝ))

/-- `QZECFIC wt0`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1372. -/
def problem067 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), ((201 / 100 : ℝ) , (y4 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x (((gamma3f_x_div_sqrtdelta ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `QZECFIC wt0 corner`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1389. -/
def problem068 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (201 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (201 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (201 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x (((gamma3f_x_div_sqrtdelta ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) >= ((0 : ℕ) : ℝ))

/-- `QZECFIC wt0 sqrt8`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1406. -/
def problem069 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (((gamma3f_x_div_sqrtdelta ((0 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((eta_y y4) y5) y6) ^ 2) > ((2 : ℕ) : ℝ)))

/-- `QZECFIC wt1`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1425. -/
def problem070 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(sqrt2 , (y1 , sqrt2)), (sqrt2 , (y2 , sqrt2)), (sqrt2 , (y3 , sqrt2)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , (((2 : ℕ) : ℝ) * hplus))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (((gamma3f_x_div_sqrtdelta (h0cut y4)) ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((1 / 125 : ℝ) * (((((((y_of_x dih4_x_div_sqrtdelta_posbranch) y1) y2) y3) y4) y5) y6))) ∨ (((((eta_y y4) y5) y6) ^ 2) > ((2 : ℕ) : ℝ)))

/-- `QZECFIC wt2 A`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1443. -/
def problem071 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(sqrt2 , (y1 , sqrt2)), (sqrt2 , (y2 , sqrt2)), (sqrt2 , (y3 , sqrt2)), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((y_of_x (((gamma3f_x_div_sqrtdelta (h0cut y4)) (h0cut y5)) ((1 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) / ((2 : ℕ) : ℝ)) > ((1 / 125 : ℝ) * (((((((y_of_x dih4_x_div_sqrtdelta_posbranch) y1) y2) y3) y4) y5) y6))) ∨ (((((eta_y y4) y5) y6) ^ 2) > ((2 : ℕ) : ℝ)))

/-- `CIHTIUM`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1462. -/
def problem072 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((eta_y y4) y5) y6) ^ 2) > ((2 : ℕ) : ℝ))

/-- `CJFZZDW`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1479. -/
def problem073 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), ((((2 : ℕ) : ℝ) * hplus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hplus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((eta_y y4) y5) y6) ^ 2) > ((2 : ℕ) : ℝ))

/-- `JSPEVYT`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1496. -/
def problem074 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (y1 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), ((((2 : ℕ) : ℝ) * hminus) , (y4 , sqrt8)), ((((2 : ℕ) : ℝ) * hminus) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((eta_y y4) y5) y6) ^ 2) > ((67 / 50 : ℝ) ^ 2))

/-- `GRKIBMP A V2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1520. -/
def problem075 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * hplus))), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x (gamma2_x1_div_a_v2 (h0cut y1))) y1) y2) y3) y4) y5) y6) > (1 / 125 : ℝ))

/-- `GRKIBMP B V2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1537. -/
def problem076 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((((2 : ℕ) : ℝ) * hplus) , (y1 , sqrt8)), (((1 : ℕ) : ℝ) , (y2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y3 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (y6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x (gamma2_x1_div_a_v2 ((0 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) >= ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 0`; spec_pass/nonlinear_ineqdata3q1h.hl:265. -/
def problem077 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129913 / 1000000 : ℝ))) + ((((-(944 / 15625 : ℝ)) + ((441 / 25000 : ℝ) + ((22583 / 500000 : ℝ) + (21777 / 1000000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y41)) + ((-(56567 / 500000 : ℝ)) + ((-(198777 / 1000000 : ℝ)) + ((-(76523 / 250000 : ℝ)) + (-(129583 / 500000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 0`; spec_pass/nonlinear_ineqdata3q1h.hl:265. -/
def problem078 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(944 / 15625 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(56567 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 0`; spec_pass/nonlinear_ineqdata3q1h.hl:265. -/
def problem079 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((441 / 25000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(198777 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 0`; spec_pass/nonlinear_ineqdata3q1h.hl:265. -/
def problem080 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((22583 / 500000 : ℝ) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(76523 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 0`; spec_pass/nonlinear_ineqdata3q1h.hl:265. -/
def problem081 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((21777 / 1000000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(129583 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 1`; spec_pass/nonlinear_ineqdata3q1h.hl:271. -/
def problem082 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129699 / 1000000 : ℝ))) + ((((-(15079 / 250000 : ℝ)) + ((9607 / 500000 : ℝ) + ((21887 / 1000000 : ℝ) + (9607 / 500000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((283 / 125000 : ℝ) + (-(283 / 125000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(283 / 125000 : ℝ)) + (283 / 125000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((283 / 125000 : ℝ) + (-(283 / 125000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(283 / 125000 : ℝ)) + (283 / 125000 : ℝ)) * y41)) + ((-(28029 / 250000 : ℝ)) + ((-(203309 / 1000000 : ℝ)) + ((-(29619 / 100000 : ℝ)) + (-(203309 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 1`; spec_pass/nonlinear_ineqdata3q1h.hl:271. -/
def problem083 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129699 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(15079 / 250000 : ℝ)) * y1) + (((283 / 125000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(28029 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 1`; spec_pass/nonlinear_ineqdata3q1h.hl:271. -/
def problem084 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129699 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9607 / 500000 : ℝ) * y1) + (((-(283 / 125000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(203309 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 1`; spec_pass/nonlinear_ineqdata3q1h.hl:271. -/
def problem085 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129699 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((21887 / 1000000 : ℝ) * y1) + (((283 / 125000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(29619 / 100000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 1`; spec_pass/nonlinear_ineqdata3q1h.hl:271. -/
def problem086 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129699 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9607 / 500000 : ℝ) * y1) + (((-(283 / 125000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(203309 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 2`; spec_pass/nonlinear_ineqdata3q1h.hl:277. -/
def problem087 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129913 / 1000000 : ℝ))) + ((((-(944 / 15625 : ℝ)) + ((21777 / 1000000 : ℝ) + ((22583 / 500000 : ℝ) + (441 / 25000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y41)) + ((-(56567 / 500000 : ℝ)) + ((-(129583 / 500000 : ℝ)) + ((-(76523 / 250000 : ℝ)) + (-(198777 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 2`; spec_pass/nonlinear_ineqdata3q1h.hl:277. -/
def problem088 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(944 / 15625 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(56567 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 2`; spec_pass/nonlinear_ineqdata3q1h.hl:277. -/
def problem089 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((21777 / 1000000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(129583 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 2`; spec_pass/nonlinear_ineqdata3q1h.hl:277. -/
def problem090 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((22583 / 500000 : ℝ) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(76523 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 2`; spec_pass/nonlinear_ineqdata3q1h.hl:277. -/
def problem091 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((441 / 25000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(198777 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 3`; spec_pass/nonlinear_ineqdata3q1h.hl:283. -/
def problem092 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(14359 / 125000 : ℝ)))) + ((((133539 / 1000000 : ℝ) + ((29721 / 200000 : ℝ) + ((8743 / 100000 : ℝ) + (29721 / 200000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(80919 / 1000000 : ℝ)) + (80919 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((80919 / 1000000 : ℝ) + (-(80919 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(80919 / 1000000 : ℝ)) + (80919 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((80919 / 1000000 : ℝ) + (-(80919 / 1000000 : ℝ))) * y41)) + ((133131 / 250000 : ℝ) + ((-(213787 / 250000 : ℝ)) + ((296861 / 500000 : ℝ) + (-(213787 / 250000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 3`; spec_pass/nonlinear_ineqdata3q1h.hl:283. -/
def problem093 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((133539 / 1000000 : ℝ) * y1) + (((-(80919 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (133131 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 3`; spec_pass/nonlinear_ineqdata3q1h.hl:283. -/
def problem094 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((29721 / 200000 : ℝ) * y1) + (((80919 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(213787 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 3`; spec_pass/nonlinear_ineqdata3q1h.hl:283. -/
def problem095 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((8743 / 100000 : ℝ) * y1) + (((-(80919 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (296861 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 3`; spec_pass/nonlinear_ineqdata3q1h.hl:283. -/
def problem096 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((29721 / 200000 : ℝ) * y1) + (((80919 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(213787 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 4`; spec_pass/nonlinear_ineqdata3q1h.hl:289. -/
def problem097 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(2183 / 250000 : ℝ)) + ((72591 / 1000000 : ℝ) + ((42651 / 1000000 : ℝ) + (13839 / 250000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(6221 / 250000 : ℝ)) + (6221 / 250000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((6221 / 250000 : ℝ) + (-(6221 / 250000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(6221 / 250000 : ℝ)) + (6221 / 250000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((6221 / 250000 : ℝ) + (-(6221 / 250000 : ℝ))) * y41)) + ((24289 / 250000 : ℝ) + ((-(464803 / 1000000 : ℝ)) + ((8797 / 1000000 : ℝ) + (-(114527 / 250000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 4`; spec_pass/nonlinear_ineqdata3q1h.hl:289. -/
def problem098 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2183 / 250000 : ℝ)) * y1) + (((-(6221 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (24289 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 4`; spec_pass/nonlinear_ineqdata3q1h.hl:289. -/
def problem099 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((72591 / 1000000 : ℝ) * y1) + (((6221 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(464803 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 4`; spec_pass/nonlinear_ineqdata3q1h.hl:289. -/
def problem100 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((42651 / 1000000 : ℝ) * y1) + (((-(6221 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (8797 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 4`; spec_pass/nonlinear_ineqdata3q1h.hl:289. -/
def problem101 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((13839 / 250000 : ℝ) * y1) + (((6221 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(114527 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 5`; spec_pass/nonlinear_ineqdata3q1h.hl:295. -/
def problem102 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(14889 / 500000 : ℝ)) + ((72591 / 1000000 : ℝ) + ((13839 / 250000 : ℝ) + (72591 / 1000000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(27449 / 1000000 : ℝ)) + (27449 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((27449 / 1000000 : ℝ) + (-(27449 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(27449 / 1000000 : ℝ)) + (27449 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((27449 / 1000000 : ℝ) + (-(27449 / 1000000 : ℝ))) * y41)) + ((170713 / 1000000 : ℝ) + ((-(485323 / 1000000 : ℝ)) + ((-(19719 / 500000 : ℝ)) + (-(485323 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 5`; spec_pass/nonlinear_ineqdata3q1h.hl:295. -/
def problem103 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14889 / 500000 : ℝ)) * y1) + (((-(27449 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (170713 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 5`; spec_pass/nonlinear_ineqdata3q1h.hl:295. -/
def problem104 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((72591 / 1000000 : ℝ) * y1) + (((27449 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(485323 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 5`; spec_pass/nonlinear_ineqdata3q1h.hl:295. -/
def problem105 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((13839 / 250000 : ℝ) * y1) + (((-(27449 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(19719 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 5`; spec_pass/nonlinear_ineqdata3q1h.hl:295. -/
def problem106 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((72591 / 1000000 : ℝ) * y1) + (((27449 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(485323 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 6`; spec_pass/nonlinear_ineqdata3q1h.hl:301. -/
def problem107 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(2183 / 250000 : ℝ)) + ((13839 / 250000 : ℝ) + ((72591 / 1000000 : ℝ) + (37947 / 1000000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((12729 / 500000 : ℝ) + (-(12729 / 500000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(12729 / 500000 : ℝ)) + (12729 / 500000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((12729 / 500000 : ℝ) + (-(12729 / 500000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(12729 / 500000 : ℝ)) + (12729 / 500000 : ℝ)) * y41)) + ((-(15279 / 50000 : ℝ)) + ((-(55371 / 1000000 : ℝ)) + ((-(469389 / 1000000 : ℝ)) + (6309 / 250000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 6`; spec_pass/nonlinear_ineqdata3q1h.hl:301. -/
def problem108 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2183 / 250000 : ℝ)) * y1) + (((12729 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(15279 / 50000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 6`; spec_pass/nonlinear_ineqdata3q1h.hl:301. -/
def problem109 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((13839 / 250000 : ℝ) * y1) + (((-(12729 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(55371 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 6`; spec_pass/nonlinear_ineqdata3q1h.hl:301. -/
def problem110 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((72591 / 1000000 : ℝ) * y1) + (((12729 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(469389 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 6`; spec_pass/nonlinear_ineqdata3q1h.hl:301. -/
def problem111 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((37947 / 1000000 : ℝ) * y1) + (((-(12729 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (6309 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 7`; spec_pass/nonlinear_ineqdata3q1h.hl:306. -/
def problem112 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(14359 / 125000 : ℝ)))) + ((((116669 / 1000000 : ℝ) + ((8743 / 100000 : ℝ) + ((29721 / 200000 : ℝ) + (8743 / 100000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((80919 / 1000000 : ℝ) + (-(80919 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(80919 / 1000000 : ℝ)) + (80919 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((80919 / 1000000 : ℝ) + (-(80919 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(80919 / 1000000 : ℝ)) + (80919 / 1000000 : ℝ)) * y41)) + ((-(7251449999999999 / 10000000000000000 : ℝ)) + ((297773 / 500000 : ℝ) + ((-(213331 / 250000 : ℝ)) + (297773 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 7`; spec_pass/nonlinear_ineqdata3q1h.hl:306. -/
def problem113 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((116669 / 1000000 : ℝ) * y1) + (((80919 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(7251449999999999 / 10000000000000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 7`; spec_pass/nonlinear_ineqdata3q1h.hl:306. -/
def problem114 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((8743 / 100000 : ℝ) * y1) + (((-(80919 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (297773 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 7`; spec_pass/nonlinear_ineqdata3q1h.hl:306. -/
def problem115 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((29721 / 200000 : ℝ) * y1) + (((80919 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(213331 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 7`; spec_pass/nonlinear_ineqdata3q1h.hl:306. -/
def problem116 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(14359 / 125000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((8743 / 100000 : ℝ) * y1) + (((-(80919 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (297773 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 8`; spec_pass/nonlinear_ineqdata3q1h.hl:312. -/
def problem117 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129913 / 1000000 : ℝ))) + ((((-(286 / 3125 : ℝ)) + ((347659 / 1000000 : ℝ) + ((-(13151 / 125000 : ℝ)) + (-(150931 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y41)) + ((-(34749 / 1000000 : ℝ)) + ((-(41217 / 40000 : ℝ)) + ((72849 / 1000000 : ℝ) + (176057 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 8`; spec_pass/nonlinear_ineqdata3q1h.hl:312. -/
def problem118 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(286 / 3125 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(34749 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 8`; spec_pass/nonlinear_ineqdata3q1h.hl:312. -/
def problem119 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((347659 / 1000000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(41217 / 40000 : ℝ))))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 8`; spec_pass/nonlinear_ineqdata3q1h.hl:312. -/
def problem120 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13151 / 125000 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (72849 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 8`; spec_pass/nonlinear_ineqdata3q1h.hl:312. -/
def problem121 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(150931 / 1000000 : ℝ)) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (176057 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 9`; spec_pass/nonlinear_ineqdata3q1h.hl:317. -/
def problem122 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129913 / 1000000 : ℝ))) + ((((68153 / 200000 : ℝ) + ((-(94917 / 1000000 : ℝ)) + ((-(150931 / 1000000 : ℝ)) + (-(94917 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y41)) + ((-(281027 / 250000 : ℝ)) + ((42433 / 500000 : ℝ) + ((34527 / 250000 : ℝ) + (42433 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 9`; spec_pass/nonlinear_ineqdata3q1h.hl:317. -/
def problem123 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((68153 / 200000 : ℝ) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(281027 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 9`; spec_pass/nonlinear_ineqdata3q1h.hl:317. -/
def problem124 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(94917 / 1000000 : ℝ)) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (42433 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 9`; spec_pass/nonlinear_ineqdata3q1h.hl:317. -/
def problem125 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(150931 / 1000000 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (34527 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 9`; spec_pass/nonlinear_ineqdata3q1h.hl:317. -/
def problem126 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(94917 / 1000000 : ℝ)) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (42433 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 10`; spec_pass/nonlinear_ineqdata3q1h.hl:322. -/
def problem127 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (129913 / 1000000 : ℝ))) + ((((-(286 / 3125 : ℝ)) + ((58329 / 200000 : ℝ) + ((-(13151 / 125000 : ℝ)) + (-(94917 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((593 / 250000 : ℝ) + (-(593 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(593 / 250000 : ℝ)) + (593 / 250000 : ℝ)) * y41)) + ((-(34749 / 1000000 : ℝ)) + ((-(469617 / 500000 : ℝ)) + ((72849 / 1000000 : ℝ) + (42433 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 10`; spec_pass/nonlinear_ineqdata3q1h.hl:322. -/
def problem128 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(286 / 3125 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(34749 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 10`; spec_pass/nonlinear_ineqdata3q1h.hl:322. -/
def problem129 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((58329 / 200000 : ℝ) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(469617 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 10`; spec_pass/nonlinear_ineqdata3q1h.hl:322. -/
def problem130 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13151 / 125000 : ℝ)) * y1) + (((593 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (72849 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 10`; spec_pass/nonlinear_ineqdata3q1h.hl:322. -/
def problem131 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((129913 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(94917 / 1000000 : ℝ)) * y1) + (((-(593 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (42433 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 11`; spec_pass/nonlinear_ineqdata3q1h.hl:328. -/
def problem132 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (64253 / 500000 : ℝ))) + ((((290371 / 1000000 : ℝ) + ((-(35439 / 500000 : ℝ)) + ((-(48829 / 500000 : ℝ)) + (-(24367 / 200000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y41)) + ((-(1026581 / 1000000 : ℝ)) + ((16697 / 500000 : ℝ) + ((50047 / 1000000 : ℝ) + (13571 / 100000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 11`; spec_pass/nonlinear_ineqdata3q1h.hl:328. -/
def problem133 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((290371 / 1000000 : ℝ) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(1026581 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 11`; spec_pass/nonlinear_ineqdata3q1h.hl:328. -/
def problem134 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(35439 / 500000 : ℝ)) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (16697 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 11`; spec_pass/nonlinear_ineqdata3q1h.hl:328. -/
def problem135 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(48829 / 500000 : ℝ)) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (50047 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 11`; spec_pass/nonlinear_ineqdata3q1h.hl:328. -/
def problem136 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(24367 / 200000 : ℝ)) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (13571 / 100000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 12`; spec_pass/nonlinear_ineqdata3q1h.hl:334. -/
def problem137 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (64253 / 500000 : ℝ))) + ((((263591 / 1000000 : ℝ) + ((-(35439 / 500000 : ℝ)) + ((-(24367 / 200000 : ℝ)) + (-(35439 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y41)) + ((-(957343 / 1000000 : ℝ)) + ((16697 / 500000 : ℝ) + ((133 / 1600 : ℝ) + (16697 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 12`; spec_pass/nonlinear_ineqdata3q1h.hl:334. -/
def problem138 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((263591 / 1000000 : ℝ) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(957343 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 12`; spec_pass/nonlinear_ineqdata3q1h.hl:334. -/
def problem139 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(35439 / 500000 : ℝ)) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (16697 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 12`; spec_pass/nonlinear_ineqdata3q1h.hl:334. -/
def problem140 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(24367 / 200000 : ℝ)) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (133 / 1600 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 12`; spec_pass/nonlinear_ineqdata3q1h.hl:334. -/
def problem141 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(35439 / 500000 : ℝ)) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (16697 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 13`; spec_pass/nonlinear_ineqdata3q1h.hl:340. -/
def problem142 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (64253 / 500000 : ℝ))) + ((((-(33127 / 500000 : ℝ)) + ((234791 / 1000000 : ℝ) + ((-(48829 / 500000 : ℝ)) + (-(35439 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((3287 / 1000000 : ℝ) + (-(3287 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(3287 / 1000000 : ℝ)) + (3287 / 1000000 : ℝ)) * y41)) + ((-(104563 / 1000000 : ℝ)) + ((-(786309 / 1000000 : ℝ)) + ((50047 / 1000000 : ℝ) + (16697 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 13`; spec_pass/nonlinear_ineqdata3q1h.hl:340. -/
def problem143 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(33127 / 500000 : ℝ)) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(104563 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 13`; spec_pass/nonlinear_ineqdata3q1h.hl:340. -/
def problem144 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((234791 / 1000000 : ℝ) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(786309 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 13`; spec_pass/nonlinear_ineqdata3q1h.hl:340. -/
def problem145 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(48829 / 500000 : ℝ)) * y1) + (((3287 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (50047 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 13`; spec_pass/nonlinear_ineqdata3q1h.hl:340. -/
def problem146 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((64253 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(35439 / 500000 : ℝ)) * y1) + (((-(3287 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (16697 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 14`; spec_pass/nonlinear_ineqdata3q1h.hl:346. -/
def problem147 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (63583 / 500000 : ℝ))) + ((((-(7331 / 100000 : ℝ)) + ((1499 / 6250 : ℝ) + ((-(96981 / 1000000 : ℝ)) + (-(17387 / 250000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((947 / 250000 : ℝ) + (-(947 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(947 / 250000 : ℝ)) + (947 / 250000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((947 / 250000 : ℝ) + (-(947 / 250000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(947 / 250000 : ℝ)) + (947 / 250000 : ℝ)) * y41)) + ((-(105909 / 1000000 : ℝ)) + ((-(767737 / 1000000 : ℝ)) + ((531 / 12500 : ℝ) + (6431 / 200000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 14`; spec_pass/nonlinear_ineqdata3q1h.hl:346. -/
def problem148 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((63583 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7331 / 100000 : ℝ)) * y1) + (((947 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(105909 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 14`; spec_pass/nonlinear_ineqdata3q1h.hl:346. -/
def problem149 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((63583 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((1499 / 6250 : ℝ) * y1) + (((-(947 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(767737 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 14`; spec_pass/nonlinear_ineqdata3q1h.hl:346. -/
def problem150 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((63583 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(96981 / 1000000 : ℝ)) * y1) + (((947 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (531 / 12500 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 14`; spec_pass/nonlinear_ineqdata3q1h.hl:346. -/
def problem151 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((63583 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(17387 / 250000 : ℝ)) * y1) + (((-(947 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (6431 / 200000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 15`; spec_pass/nonlinear_ineqdata3q1h.hl:352. -/
def problem152 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (126777 / 1000000 : ℝ))) + ((((-(53069 / 1000000 : ℝ)) + ((98233 / 500000 : ℝ) + ((-(23383 / 250000 : ℝ)) + (-(9973 / 200000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((141 / 40000 : ℝ) + (-(141 / 40000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(141 / 40000 : ℝ)) + (141 / 40000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((141 / 40000 : ℝ) + (-(141 / 40000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(141 / 40000 : ℝ)) + (141 / 40000 : ℝ)) * y41)) + ((-(35663 / 250000 : ℝ)) + ((-(667227 / 1000000 : ℝ)) + ((17811 / 500000 : ℝ) + (-(22307 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 15`; spec_pass/nonlinear_ineqdata3q1h.hl:352. -/
def problem153 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((126777 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(53069 / 1000000 : ℝ)) * y1) + (((141 / 40000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(35663 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 15`; spec_pass/nonlinear_ineqdata3q1h.hl:352. -/
def problem154 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((126777 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((98233 / 500000 : ℝ) * y1) + (((-(141 / 40000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(667227 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 15`; spec_pass/nonlinear_ineqdata3q1h.hl:352. -/
def problem155 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((126777 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(23383 / 250000 : ℝ)) * y1) + (((141 / 40000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (17811 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 15`; spec_pass/nonlinear_ineqdata3q1h.hl:352. -/
def problem156 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((126777 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(9973 / 200000 : ℝ)) * y1) + (((-(141 / 40000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(22307 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 16`; spec_pass/nonlinear_ineqdata3q1h.hl:359. -/
def problem157 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(14413 / 1000000 : ℝ)) + ((-(14413 / 1000000 : ℝ)) + (-(2241 / 100000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y41)) + ((-(530637 / 1000000 : ℝ)) + ((594377 / 1000000 : ℝ) + ((-(377571 / 1000000 : ℝ)) + (608509 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 16`; spec_pass/nonlinear_ineqdata3q1h.hl:359. -/
def problem158 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(530637 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 16`; spec_pass/nonlinear_ineqdata3q1h.hl:359. -/
def problem159 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 16`; spec_pass/nonlinear_ineqdata3q1h.hl:359. -/
def problem160 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(377571 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 16`; spec_pass/nonlinear_ineqdata3q1h.hl:359. -/
def problem161 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (608509 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 17`; spec_pass/nonlinear_ineqdata3q1h.hl:366. -/
def problem162 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(14413 / 1000000 : ℝ)) + ((-(2241 / 100000 : ℝ)) + (-(14413 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y41)) + ((-(132659 / 250000 : ℝ)) + ((594377 / 1000000 : ℝ) + ((-(4543 / 12500 : ℝ)) + (594377 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 17`; spec_pass/nonlinear_ineqdata3q1h.hl:366. -/
def problem163 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(132659 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 17`; spec_pass/nonlinear_ineqdata3q1h.hl:366. -/
def problem164 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 17`; spec_pass/nonlinear_ineqdata3q1h.hl:366. -/
def problem165 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(4543 / 12500 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 17`; spec_pass/nonlinear_ineqdata3q1h.hl:366. -/
def problem166 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 18`; spec_pass/nonlinear_ineqdata3q1h.hl:373. -/
def problem167 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(2241 / 100000 : ℝ)) + ((-(14413 / 1000000 : ℝ)) + (-(14413 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y41)) + ((-(530637 / 1000000 : ℝ)) + ((608509 / 1000000 : ℝ) + ((-(377571 / 1000000 : ℝ)) + (594377 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 18`; spec_pass/nonlinear_ineqdata3q1h.hl:373. -/
def problem168 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(530637 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 18`; spec_pass/nonlinear_ineqdata3q1h.hl:373. -/
def problem169 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (608509 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 18`; spec_pass/nonlinear_ineqdata3q1h.hl:373. -/
def problem170 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(377571 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 18`; spec_pass/nonlinear_ineqdata3q1h.hl:373. -/
def problem171 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 19`; spec_pass/nonlinear_ineqdata3q1h.hl:379. -/
def problem172 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(36939 / 1000000 : ℝ)))) + ((((3129 / 62500 : ℝ) + ((-(1043 / 62500 : ℝ)) + ((-(1043 / 62500 : ℝ)) + (-(1043 / 62500 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(57593 / 1000000 : ℝ)) + (57593 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((57593 / 1000000 : ℝ) + (-(57593 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(57593 / 1000000 : ℝ)) + (-(57593 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(57593 / 1000000 : ℝ)) + (-(57593 / 1000000 : ℝ))) * y41)) + ((99471 / 250000 : ℝ) + ((-(362427 / 1000000 : ℝ)) + ((279531 / 500000 : ℝ) + (279531 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 19`; spec_pass/nonlinear_ineqdata3q1h.hl:379. -/
def problem173 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((3129 / 62500 : ℝ) * y1) + (((-(57593 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (99471 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 19`; spec_pass/nonlinear_ineqdata3q1h.hl:379. -/
def problem174 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((57593 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(362427 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 19`; spec_pass/nonlinear_ineqdata3q1h.hl:379. -/
def problem175 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((-(57593 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (279531 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 19`; spec_pass/nonlinear_ineqdata3q1h.hl:379. -/
def problem176 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((-(57593 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (279531 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 20`; spec_pass/nonlinear_ineqdata3q1h.hl:385. -/
def problem177 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(49823 / 1000000 : ℝ)))) + ((((11763 / 250000 : ℝ) + ((-(3921 / 250000 : ℝ)) + ((-(3921 / 250000 : ℝ)) + (-(3921 / 250000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(61687 / 1000000 : ℝ)) + (61687 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((61687 / 1000000 : ℝ) + (-(61687 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(61687 / 1000000 : ℝ)) + (61687 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((61687 / 1000000 : ℝ) + (-(61687 / 1000000 : ℝ))) * y41)) + ((231811 / 500000 : ℝ) + ((-(379191 / 1000000 : ℝ)) + ((607807 / 1000000 : ℝ) + (-(379191 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 20`; spec_pass/nonlinear_ineqdata3q1h.hl:385. -/
def problem178 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(49823 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((11763 / 250000 : ℝ) * y1) + (((-(61687 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (231811 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 20`; spec_pass/nonlinear_ineqdata3q1h.hl:385. -/
def problem179 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(49823 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(3921 / 250000 : ℝ)) * y1) + (((61687 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(379191 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 20`; spec_pass/nonlinear_ineqdata3q1h.hl:385. -/
def problem180 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(49823 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(3921 / 250000 : ℝ)) * y1) + (((-(61687 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (607807 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 20`; spec_pass/nonlinear_ineqdata3q1h.hl:385. -/
def problem181 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(49823 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(3921 / 250000 : ℝ)) * y1) + (((61687 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(379191 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 21`; spec_pass/nonlinear_ineqdata3q1h.hl:391. -/
def problem182 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(26791 / 500000 : ℝ)))) + ((((12363 / 250000 : ℝ) + ((-(13853 / 1000000 : ℝ)) + ((-(20791 / 1000000 : ℝ)) + (-(13853 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(3151 / 50000 : ℝ)) + (3151 / 50000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((3151 / 50000 : ℝ) + (-(3151 / 50000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(3151 / 50000 : ℝ)) + (-(62897 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(62897 / 1000000 : ℝ)) + (-(3151 / 50000 : ℝ))) * y41)) + ((237757 / 500000 : ℝ) + ((-(194617 / 500000 : ℝ)) + ((159283 / 250000 : ℝ) + (618101 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 21`; spec_pass/nonlinear_ineqdata3q1h.hl:391. -/
def problem183 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(26791 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((12363 / 250000 : ℝ) * y1) + (((-(3151 / 50000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (237757 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 21`; spec_pass/nonlinear_ineqdata3q1h.hl:391. -/
def problem184 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(26791 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13853 / 1000000 : ℝ)) * y1) + (((3151 / 50000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(194617 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 21`; spec_pass/nonlinear_ineqdata3q1h.hl:391. -/
def problem185 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(26791 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(20791 / 1000000 : ℝ)) * y1) + (((-(3151 / 50000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (159283 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 21`; spec_pass/nonlinear_ineqdata3q1h.hl:391. -/
def problem186 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(26791 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13853 / 1000000 : ℝ)) * y1) + (((-(62897 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (618101 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 22`; spec_pass/nonlinear_ineqdata3q1h.hl:397. -/
def problem187 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(13387 / 200000 : ℝ)))) + ((((79693 / 1000000 : ℝ) + ((-(4299 / 200000 : ℝ)) + ((-(4299 / 200000 : ℝ)) + (-(1147 / 31250 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y41)) + ((-(605497 / 1000000 : ℝ)) + ((171327 / 250000 : ℝ) + ((-(374549 / 1000000 : ℝ)) + (89413 / 125000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 22`; spec_pass/nonlinear_ineqdata3q1h.hl:397. -/
def problem188 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((79693 / 1000000 : ℝ) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(605497 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 22`; spec_pass/nonlinear_ineqdata3q1h.hl:397. -/
def problem189 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (171327 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 22`; spec_pass/nonlinear_ineqdata3q1h.hl:397. -/
def problem190 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(374549 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 22`; spec_pass/nonlinear_ineqdata3q1h.hl:397. -/
def problem191 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1147 / 31250 : ℝ)) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (89413 / 125000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 23`; spec_pass/nonlinear_ineqdata3q1h.hl:403. -/
def problem192 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(13387 / 200000 : ℝ)))) + ((((28887 / 1000000 : ℝ) + ((-(4299 / 200000 : ℝ)) + ((7051 / 500000 : ℝ) + (-(4299 / 200000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y41)) + ((-(238733 / 500000 : ℝ)) + ((171327 / 250000 : ℝ) + ((-(59073 / 125000 : ℝ)) + (171327 / 250000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 23`; spec_pass/nonlinear_ineqdata3q1h.hl:403. -/
def problem193 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((28887 / 1000000 : ℝ) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(238733 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 23`; spec_pass/nonlinear_ineqdata3q1h.hl:403. -/
def problem194 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (171327 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 23`; spec_pass/nonlinear_ineqdata3q1h.hl:403. -/
def problem195 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((7051 / 500000 : ℝ) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(59073 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 23`; spec_pass/nonlinear_ineqdata3q1h.hl:403. -/
def problem196 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (171327 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 24`; spec_pass/nonlinear_ineqdata3q1h.hl:409. -/
def problem197 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(13387 / 200000 : ℝ)))) + ((((28887 / 1000000 : ℝ) + ((7051 / 500000 : ℝ) + ((-(4299 / 200000 : ℝ)) + (-(4299 / 200000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(66241 / 1000000 : ℝ)) + (66241 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((66241 / 1000000 : ℝ) + (-(66241 / 1000000 : ℝ))) * y41)) + ((582391 / 1000000 : ℝ) + ((-(59073 / 125000 : ℝ)) + ((171327 / 250000 : ℝ) + (-(374549 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 24`; spec_pass/nonlinear_ineqdata3q1h.hl:409. -/
def problem198 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((28887 / 1000000 : ℝ) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (582391 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 24`; spec_pass/nonlinear_ineqdata3q1h.hl:409. -/
def problem199 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((7051 / 500000 : ℝ) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(59073 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 24`; spec_pass/nonlinear_ineqdata3q1h.hl:409. -/
def problem200 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((-(66241 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (171327 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 24`; spec_pass/nonlinear_ineqdata3q1h.hl:409. -/
def problem201 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(13387 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4299 / 200000 : ℝ)) * y1) + (((66241 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(374549 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 25`; spec_pass/nonlinear_ineqdata3q1h.hl:415. -/
def problem202 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(70081 / 1000000 : ℝ)))) + ((((1721 / 40000 : ℝ) + ((-(7171 / 500000 : ℝ)) + ((-(7171 / 500000 : ℝ)) + (-(7171 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((271 / 4000 : ℝ) + (-(271 / 4000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(271 / 4000 : ℝ)) + (271 / 4000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((271 / 4000 : ℝ) + (-(271 / 4000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(271 / 4000 : ℝ)) + (271 / 4000 : ℝ)) * y41)) + ((-(260499 / 500000 : ℝ)) + ((340889 / 500000 : ℝ) + ((-(100557 / 250000 : ℝ)) + (340889 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 25`; spec_pass/nonlinear_ineqdata3q1h.hl:415. -/
def problem203 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(70081 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((1721 / 40000 : ℝ) * y1) + (((271 / 4000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(260499 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 25`; spec_pass/nonlinear_ineqdata3q1h.hl:415. -/
def problem204 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(70081 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7171 / 500000 : ℝ)) * y1) + (((-(271 / 4000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (340889 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 25`; spec_pass/nonlinear_ineqdata3q1h.hl:415. -/
def problem205 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(70081 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7171 / 500000 : ℝ)) * y1) + (((271 / 4000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(100557 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 25`; spec_pass/nonlinear_ineqdata3q1h.hl:415. -/
def problem206 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(70081 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7171 / 500000 : ℝ)) * y1) + (((-(271 / 4000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (340889 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 26`; spec_pass/nonlinear_ineqdata3q1h.hl:421. -/
def problem207 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(74623 / 1000000 : ℝ)))) + ((((15871 / 200000 : ℝ) + ((-(23711 / 1000000 : ℝ)) + ((-(23711 / 1000000 : ℝ)) + (-(7983 / 250000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((13719 / 200000 : ℝ) + (-(13719 / 200000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(13719 / 200000 : ℝ)) + (13719 / 200000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((13719 / 200000 : ℝ) + (-(13719 / 200000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(13719 / 200000 : ℝ)) + (13719 / 200000 : ℝ)) * y41)) + ((-(608613 / 1000000 : ℝ)) + ((719631 / 1000000 : ℝ) + ((-(37789 / 100000 : ℝ)) + (367869 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 26`; spec_pass/nonlinear_ineqdata3q1h.hl:421. -/
def problem208 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((15871 / 200000 : ℝ) * y1) + (((13719 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(608613 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 26`; spec_pass/nonlinear_ineqdata3q1h.hl:421. -/
def problem209 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(23711 / 1000000 : ℝ)) * y1) + (((-(13719 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (719631 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 26`; spec_pass/nonlinear_ineqdata3q1h.hl:421. -/
def problem210 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(23711 / 1000000 : ℝ)) * y1) + (((13719 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(37789 / 100000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 26`; spec_pass/nonlinear_ineqdata3q1h.hl:421. -/
def problem211 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7983 / 250000 : ℝ)) * y1) + (((-(13719 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (367869 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 27`; spec_pass/nonlinear_ineqdata3q1h.hl:427. -/
def problem212 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(74623 / 1000000 : ℝ)))) + ((((9851 / 500000 : ℝ) + ((-(23711 / 1000000 : ℝ)) + ((-(7983 / 250000 : ℝ)) + (17971 / 500000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(20301 / 250000 : ℝ)) + (20301 / 250000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((20301 / 250000 : ℝ) + (-(20301 / 250000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(20301 / 250000 : ℝ)) + (20301 / 250000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((20301 / 250000 : ℝ) + (-(20301 / 250000 : ℝ))) * y41)) + ((148021 / 200000 : ℝ) + ((-(11969 / 25000 : ℝ)) + ((13072 / 15625 : ℝ) + (-(314543 / 500000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 27`; spec_pass/nonlinear_ineqdata3q1h.hl:427. -/
def problem213 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9851 / 500000 : ℝ) * y1) + (((-(20301 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (148021 / 200000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 27`; spec_pass/nonlinear_ineqdata3q1h.hl:427. -/
def problem214 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(23711 / 1000000 : ℝ)) * y1) + (((20301 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(11969 / 25000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 27`; spec_pass/nonlinear_ineqdata3q1h.hl:427. -/
def problem215 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7983 / 250000 : ℝ)) * y1) + (((-(20301 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (13072 / 15625 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 27`; spec_pass/nonlinear_ineqdata3q1h.hl:427. -/
def problem216 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((17971 / 500000 : ℝ) * y1) + (((20301 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(314543 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 28`; spec_pass/nonlinear_ineqdata3q1h.hl:433. -/
def problem217 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(74623 / 1000000 : ℝ)))) + ((((9851 / 500000 : ℝ) + ((-(7983 / 250000 : ℝ)) + ((-(23711 / 1000000 : ℝ)) + (17971 / 500000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(13719 / 200000 : ℝ)) + (13719 / 200000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((13719 / 200000 : ℝ) + (-(13719 / 200000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(13719 / 200000 : ℝ)) + (13719 / 200000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((13719 / 200000 : ℝ) + (-(13719 / 200000 : ℝ))) * y41)) + ((639237 / 1000000 : ℝ) + ((-(45223 / 125000 : ℝ)) + ((719631 / 1000000 : ℝ) + (-(528217 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 28`; spec_pass/nonlinear_ineqdata3q1h.hl:433. -/
def problem218 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9851 / 500000 : ℝ) * y1) + (((-(13719 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (639237 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 28`; spec_pass/nonlinear_ineqdata3q1h.hl:433. -/
def problem219 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7983 / 250000 : ℝ)) * y1) + (((13719 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(45223 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 28`; spec_pass/nonlinear_ineqdata3q1h.hl:433. -/
def problem220 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(23711 / 1000000 : ℝ)) * y1) + (((-(13719 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (719631 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 28`; spec_pass/nonlinear_ineqdata3q1h.hl:433. -/
def problem221 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(74623 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((17971 / 500000 : ℝ) * y1) + (((13719 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(528217 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 29`; spec_pass/nonlinear_ineqdata3q1h.hl:439. -/
def problem222 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(90009 / 1000000 : ℝ)))) + ((((4151 / 100000 : ℝ) + ((-(13837 / 1000000 : ℝ)) + ((-(13837 / 1000000 : ℝ)) + (-(13837 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((14733 / 200000 : ℝ) + (-(14733 / 200000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(14733 / 200000 : ℝ)) + (14733 / 200000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((14733 / 200000 : ℝ) + (-(14733 / 200000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(14733 / 200000 : ℝ)) + (14733 / 200000 : ℝ)) * y41)) + ((-(261729 / 500000 : ℝ)) + ((755879 / 1000000 : ℝ) + ((-(84551 / 200000 : ℝ)) + (755879 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 29`; spec_pass/nonlinear_ineqdata3q1h.hl:439. -/
def problem223 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(90009 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((4151 / 100000 : ℝ) * y1) + (((14733 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(261729 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 29`; spec_pass/nonlinear_ineqdata3q1h.hl:439. -/
def problem224 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(90009 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13837 / 1000000 : ℝ)) * y1) + (((-(14733 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (755879 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 29`; spec_pass/nonlinear_ineqdata3q1h.hl:439. -/
def problem225 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(90009 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13837 / 1000000 : ℝ)) * y1) + (((14733 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(84551 / 200000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 29`; spec_pass/nonlinear_ineqdata3q1h.hl:439. -/
def problem226 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(90009 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(13837 / 1000000 : ℝ)) * y1) + (((-(14733 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (755879 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 30`; spec_pass/nonlinear_ineqdata3q1h.hl:445. -/
def problem227 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(681 / 4000 : ℝ)))) + ((((94709 / 1000000 : ℝ) + ((-(4291 / 200000 : ℝ)) + ((9749 / 1000000 : ℝ) + (-(4291 / 200000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((19707 / 200000 : ℝ) + (-(19707 / 200000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(19707 / 200000 : ℝ)) + (19707 / 200000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((19707 / 200000 : ℝ) + (-(19707 / 200000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(19707 / 200000 : ℝ)) + (19707 / 200000 : ℝ)) * y41)) + ((-(346017 / 500000 : ℝ)) + ((543557 / 500000 : ℝ) + ((-(568591 / 1000000 : ℝ)) + (543557 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 30`; spec_pass/nonlinear_ineqdata3q1h.hl:445. -/
def problem228 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y4 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(681 / 4000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((94709 / 1000000 : ℝ) * y1) + (((19707 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(346017 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 30`; spec_pass/nonlinear_ineqdata3q1h.hl:445. -/
def problem229 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(681 / 4000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4291 / 200000 : ℝ)) * y1) + (((-(19707 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (543557 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 30`; spec_pass/nonlinear_ineqdata3q1h.hl:445. -/
def problem230 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(681 / 4000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9749 / 1000000 : ℝ) * y1) + (((19707 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(568591 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 30`; spec_pass/nonlinear_ineqdata3q1h.hl:445. -/
def problem231 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(681 / 4000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4291 / 200000 : ℝ)) * y1) + (((-(19707 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (543557 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 31`; spec_pass/nonlinear_ineqdata3q1h.hl:451. -/
def problem232 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(86083 / 500000 : ℝ)))) + ((((9973 / 100000 : ℝ) + ((14169 / 1000000 : ℝ) + ((-(17353 / 1000000 : ℝ)) + (14169 / 1000000 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(19957 / 200000 : ℝ)) + (19957 / 200000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((19957 / 200000 : ℝ) + (-(19957 / 200000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(19957 / 200000 : ℝ)) + (19957 / 200000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((19957 / 200000 : ℝ) + (-(19957 / 200000 : ℝ))) * y41)) + ((220571 / 250000 : ℝ) + ((-(73341 / 125000 : ℝ)) + ((10903 / 10000 : ℝ) + (-(73341 / 125000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 31`; spec_pass/nonlinear_ineqdata3q1h.hl:451. -/
def problem233 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(86083 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((9973 / 100000 : ℝ) * y1) + (((-(19957 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (220571 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 31`; spec_pass/nonlinear_ineqdata3q1h.hl:451. -/
def problem234 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(86083 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((14169 / 1000000 : ℝ) * y1) + (((19957 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(73341 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 31`; spec_pass/nonlinear_ineqdata3q1h.hl:451. -/
def problem235 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(86083 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(17353 / 1000000 : ℝ)) * y1) + (((-(19957 / 200000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (10903 / 10000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 31`; spec_pass/nonlinear_ineqdata3q1h.hl:451. -/
def problem236 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(86083 / 500000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((14169 / 1000000 : ℝ) * y1) + (((19957 / 200000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(73341 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 32`; spec_pass/nonlinear_ineqdata3q1h.hl:457. -/
def problem237 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(84789 / 1000000 : ℝ)))) + ((((7969 / 200000 : ℝ) + ((-(6641 / 500000 : ℝ)) + ((-(6641 / 500000 : ℝ)) + (-(6641 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(17927 / 250000 : ℝ)) + (-(17927 / 250000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(17927 / 250000 : ℝ)) + (-(17927 / 250000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(17927 / 250000 : ℝ)) + (17927 / 250000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((17927 / 250000 : ℝ) + (-(17927 / 250000 : ℝ))) * y41)) + ((632521 / 1000000 : ℝ) + ((91453 / 125000 : ℝ) + ((91453 / 125000 : ℝ) + (-(415701 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 32`; spec_pass/nonlinear_ineqdata3q1h.hl:457. -/
def problem238 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(84789 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((7969 / 200000 : ℝ) * y1) + (((-(17927 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (632521 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 32`; spec_pass/nonlinear_ineqdata3q1h.hl:457. -/
def problem239 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(84789 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6641 / 500000 : ℝ)) * y1) + (((-(17927 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (91453 / 125000 : ℝ)))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 32`; spec_pass/nonlinear_ineqdata3q1h.hl:457. -/
def problem240 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(84789 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6641 / 500000 : ℝ)) * y1) + (((-(17927 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (91453 / 125000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 32`; spec_pass/nonlinear_ineqdata3q1h.hl:457. -/
def problem241 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(84789 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6641 / 500000 : ℝ)) * y1) + (((17927 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(415701 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 33`; spec_pass/nonlinear_ineqdata3q1h.hl:463. -/
def problem242 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(52337 / 1000000 : ℝ)) + ((11927 / 50000 : ℝ) + ((-(73933 / 1000000 : ℝ)) + (-(11227 / 100000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y41)) + ((95663 / 500000 : ℝ) + ((-(433639 / 500000 : ℝ)) + ((286871 / 1000000 : ℝ) + (-(9987 / 500000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 33`; spec_pass/nonlinear_ineqdata3q1h.hl:463. -/
def problem243 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(52337 / 1000000 : ℝ)) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (95663 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 33`; spec_pass/nonlinear_ineqdata3q1h.hl:463. -/
def problem244 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((11927 / 50000 : ℝ) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(433639 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 33`; spec_pass/nonlinear_ineqdata3q1h.hl:463. -/
def problem245 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(73933 / 1000000 : ℝ)) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (286871 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 33`; spec_pass/nonlinear_ineqdata3q1h.hl:463. -/
def problem246 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(11227 / 100000 : ℝ)) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(9987 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 34`; spec_pass/nonlinear_ineqdata3q1h.hl:468. -/
def problem247 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(52337 / 1000000 : ℝ)) + ((11927 / 50000 : ℝ) + ((-(11227 / 100000 : ℝ)) + (-(73933 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y41)) + ((-(17539 / 100000 : ℝ)) + ((-(250281 / 500000 : ℝ)) + ((-(9987 / 500000 : ℝ)) + (286871 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 34`; spec_pass/nonlinear_ineqdata3q1h.hl:468. -/
def problem248 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(52337 / 1000000 : ℝ)) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(17539 / 100000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 34`; spec_pass/nonlinear_ineqdata3q1h.hl:468. -/
def problem249 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((11927 / 50000 : ℝ) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(250281 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 34`; spec_pass/nonlinear_ineqdata3q1h.hl:468. -/
def problem250 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(11227 / 100000 : ℝ)) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(9987 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 34`; spec_pass/nonlinear_ineqdata3q1h.hl:468. -/
def problem251 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(73933 / 1000000 : ℝ)) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (286871 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 35`; spec_pass/nonlinear_ineqdata3q1h.hl:474. -/
def problem252 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (65103 / 1000000 : ℝ))) + ((((-(52337 / 1000000 : ℝ)) + ((-(11227 / 100000 : ℝ)) + ((11927 / 50000 : ℝ) + (-(73933 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((573 / 25000 : ℝ) + (-(573 / 25000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(573 / 25000 : ℝ)) + (573 / 25000 : ℝ)) * y41)) + ((-(175391 / 1000000 : ℝ)) + ((346743 / 1000000 : ℝ) + ((-(433639 / 500000 : ℝ)) + (286871 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 35`; spec_pass/nonlinear_ineqdata3q1h.hl:474. -/
def problem253 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(52337 / 1000000 : ℝ)) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(175391 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 35`; spec_pass/nonlinear_ineqdata3q1h.hl:474. -/
def problem254 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(11227 / 100000 : ℝ)) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (346743 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 35`; spec_pass/nonlinear_ineqdata3q1h.hl:474. -/
def problem255 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((11927 / 50000 : ℝ) * y1) + (((573 / 25000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(433639 / 500000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 35`; spec_pass/nonlinear_ineqdata3q1h.hl:474. -/
def problem256 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((65103 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(73933 / 1000000 : ℝ)) * y1) + (((-(573 / 25000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (286871 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 36`; spec_pass/nonlinear_ineqdata3q1h.hl:479. -/
def problem257 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (62681 / 1000000 : ℝ))) + ((((-(26929 / 1000000 : ℝ)) + ((-(6441 / 100000 : ℝ)) + ((35249 / 200000 : ℝ) + (-(42453 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y41)) + ((-(48563 / 200000 : ℝ)) + ((8549 / 31250 : ℝ) + ((-(72849 / 100000 : ℝ)) + (3039 / 10000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 36`; spec_pass/nonlinear_ineqdata3q1h.hl:479. -/
def problem258 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(26929 / 1000000 : ℝ)) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(48563 / 200000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 36`; spec_pass/nonlinear_ineqdata3q1h.hl:479. -/
def problem259 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6441 / 100000 : ℝ)) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (8549 / 31250 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 36`; spec_pass/nonlinear_ineqdata3q1h.hl:479. -/
def problem260 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((35249 / 200000 : ℝ) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(72849 / 100000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 36`; spec_pass/nonlinear_ineqdata3q1h.hl:479. -/
def problem261 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(42453 / 500000 : ℝ)) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (3039 / 10000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 37`; spec_pass/nonlinear_ineqdata3q1h.hl:485. -/
def problem262 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (62681 / 1000000 : ℝ))) + ((((-(26929 / 1000000 : ℝ)) + ((35249 / 200000 : ℝ) + ((-(42453 / 500000 : ℝ)) + (-(6441 / 100000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y41)) + ((-(48563 / 200000 : ℝ)) + ((-(348621 / 1000000 : ℝ)) + ((-(75969 / 1000000 : ℝ)) + (8549 / 31250 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 37`; spec_pass/nonlinear_ineqdata3q1h.hl:485. -/
def problem263 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(26929 / 1000000 : ℝ)) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(48563 / 200000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 37`; spec_pass/nonlinear_ineqdata3q1h.hl:485. -/
def problem264 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((35249 / 200000 : ℝ) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (-(348621 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 37`; spec_pass/nonlinear_ineqdata3q1h.hl:485. -/
def problem265 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(42453 / 500000 : ℝ)) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(75969 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 37`; spec_pass/nonlinear_ineqdata3q1h.hl:485. -/
def problem266 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6441 / 100000 : ℝ)) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (8549 / 31250 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 38`; spec_pass/nonlinear_ineqdata3q1h.hl:491. -/
def problem267 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (62681 / 1000000 : ℝ))) + ((((-(26929 / 1000000 : ℝ)) + ((-(42453 / 500000 : ℝ)) + ((35249 / 200000 : ℝ) + (-(6441 / 100000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((11871 / 500000 : ℝ) + (-(11871 / 500000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(11871 / 500000 : ℝ)) + (11871 / 500000 : ℝ)) * y41)) + ((-(48563 / 200000 : ℝ)) + ((3039 / 10000 : ℝ) + ((-(72849 / 100000 : ℝ)) + (8549 / 31250 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 38`; spec_pass/nonlinear_ineqdata3q1h.hl:491. -/
def problem268 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(26929 / 1000000 : ℝ)) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(48563 / 200000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 38`; spec_pass/nonlinear_ineqdata3q1h.hl:491. -/
def problem269 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(42453 / 500000 : ℝ)) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (3039 / 10000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 38`; spec_pass/nonlinear_ineqdata3q1h.hl:491. -/
def problem270 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((35249 / 200000 : ℝ) * y1) + (((11871 / 500000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(72849 / 100000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 38`; spec_pass/nonlinear_ineqdata3q1h.hl:491. -/
def problem271 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((62681 / 1000000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(6441 / 100000 : ℝ)) * y1) + (((-(11871 / 500000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (8549 / 31250 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 39`; spec_pass/nonlinear_ineqdata3q1h.hl:497. -/
def problem272 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (30857 / 500000 : ℝ))) + ((((-(7251 / 500000 : ℝ)) + ((67133 / 500000 : ℝ) + ((-(29941 / 500000 : ℝ)) + (-(29941 / 500000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(2407 / 100000 : ℝ)) + (2407 / 100000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((2407 / 100000 : ℝ) + (-(2407 / 100000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(2407 / 100000 : ℝ)) + (-(2407 / 100000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(2407 / 100000 : ℝ)) + (-(2407 / 100000 : ℝ))) * y41)) + ((104941 / 1000000 : ℝ) + ((-(631477 / 1000000 : ℝ)) + ((261947 / 1000000 : ℝ) + (261947 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 39`; spec_pass/nonlinear_ineqdata3q1h.hl:497. -/
def problem273 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((30857 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(7251 / 500000 : ℝ)) * y1) + (((-(2407 / 100000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (104941 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 39`; spec_pass/nonlinear_ineqdata3q1h.hl:497. -/
def problem274 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((30857 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((67133 / 500000 : ℝ) * y1) + (((2407 / 100000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(631477 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 39`; spec_pass/nonlinear_ineqdata3q1h.hl:497. -/
def problem275 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((30857 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(29941 / 500000 : ℝ)) * y1) + (((-(2407 / 100000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (261947 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 39`; spec_pass/nonlinear_ineqdata3q1h.hl:497. -/
def problem276 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((2 : ℕ) : ℝ) * hplus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((30857 / 500000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(29941 / 500000 : ℝ)) * y1) + (((-(2407 / 100000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (261947 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 40`; spec_pass/nonlinear_ineqdata3q1h.hl:503. -/
def problem277 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(14413 / 1000000 : ℝ)) + ((-(14413 / 1000000 : ℝ)) + (-(2241 / 100000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y41)) + ((-(530637 / 1000000 : ℝ)) + ((594377 / 1000000 : ℝ) + ((-(377571 / 1000000 : ℝ)) + (608509 / 1000000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 40`; spec_pass/nonlinear_ineqdata3q1h.hl:503. -/
def problem278 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(530637 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 40`; spec_pass/nonlinear_ineqdata3q1h.hl:503. -/
def problem279 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `OXLZLEZ 6346351218 3 40`; spec_pass/nonlinear_ineqdata3q1h.hl:503. -/
def problem280 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(377571 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 40`; spec_pass/nonlinear_ineqdata3q1h.hl:503. -/
def problem281 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (608509 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 41`; spec_pass/nonlinear_ineqdata3q1h.hl:510. -/
def problem282 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(14413 / 1000000 : ℝ)) + ((-(2241 / 100000 : ℝ)) + (-(14413 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(73427 / 1000000 : ℝ)) + (73427 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((73427 / 1000000 : ℝ) + (-(73427 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(73427 / 1000000 : ℝ)) + (73427 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((73427 / 1000000 : ℝ) + (-(73427 / 1000000 : ℝ))) * y41)) + ((135689 / 250000 : ℝ) + ((-(59877 / 125000 : ℝ)) + ((354977 / 500000 : ℝ) + (-(59877 / 125000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 41`; spec_pass/nonlinear_ineqdata3q1h.hl:510. -/
def problem283 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((-(73427 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (135689 / 250000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 41`; spec_pass/nonlinear_ineqdata3q1h.hl:510. -/
def problem284 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((73427 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(59877 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 41`; spec_pass/nonlinear_ineqdata3q1h.hl:510. -/
def problem285 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((-(73427 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (354977 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 41`; spec_pass/nonlinear_ineqdata3q1h.hl:510. -/
def problem286 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((73427 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(59877 / 125000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 42`; spec_pass/nonlinear_ineqdata3q1h.hl:516. -/
def problem287 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(469 / 10000 : ℝ)))) + ((((51237 / 1000000 : ℝ) + ((-(2241 / 100000 : ℝ)) + ((-(14413 / 1000000 : ℝ)) + (-(14413 / 1000000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(60747 / 1000000 : ℝ)) + (60747 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((60747 / 1000000 : ℝ) + (-(60747 / 1000000 : ℝ))) * y41)) + ((11032800000000001 / 25000000000000000 : ℝ) + ((-(4543 / 12500 : ℝ)) + ((594377 / 1000000 : ℝ) + (-(377571 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 42`; spec_pass/nonlinear_ineqdata3q1h.hl:516. -/
def problem288 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((51237 / 1000000 : ℝ) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (11032800000000001 / 25000000000000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 42`; spec_pass/nonlinear_ineqdata3q1h.hl:516. -/
def problem289 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(2241 / 100000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(4543 / 12500 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 42`; spec_pass/nonlinear_ineqdata3q1h.hl:516. -/
def problem290 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((-(60747 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (594377 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 42`; spec_pass/nonlinear_ineqdata3q1h.hl:516. -/
def problem291 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(469 / 10000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(14413 / 1000000 : ℝ)) * y1) + (((60747 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(377571 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 43`; spec_pass/nonlinear_ineqdata3q1h.hl:523. -/
def problem292 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(36939 / 1000000 : ℝ)))) + ((((3129 / 62500 : ℝ) + ((-(1043 / 62500 : ℝ)) + ((-(1043 / 62500 : ℝ)) + (-(1043 / 62500 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((57593 / 1000000 : ℝ) + (-(57593 / 1000000 : ℝ))) * y12)) + ((((2 : ℕ) : ℝ) * (((-(57593 / 1000000 : ℝ)) + (57593 / 1000000 : ℝ)) * y23)) + ((((2 : ℕ) : ℝ) * (((57593 / 1000000 : ℝ) + (-(57593 / 1000000 : ℝ))) * y34)) + ((((2 : ℕ) : ℝ) * (((-(57593 / 1000000 : ℝ)) + (57593 / 1000000 : ℝ)) * y41)) + ((-(130901 / 250000 : ℝ)) + ((279531 / 500000 : ℝ) + ((-(362427 / 1000000 : ℝ)) + (279531 / 500000 : ℝ)))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 43`; spec_pass/nonlinear_ineqdata3q1h.hl:523. -/
def problem293 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((3129 / 62500 : ℝ) * y1) + (((57593 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(130901 / 250000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 43`; spec_pass/nonlinear_ineqdata3q1h.hl:523. -/
def problem294 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((-(57593 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (279531 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 43`; spec_pass/nonlinear_ineqdata3q1h.hl:523. -/
def problem295 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((57593 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(362427 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 43`; spec_pass/nonlinear_ineqdata3q1h.hl:523. -/
def problem296 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(36939 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(1043 / 62500 : ℝ)) * y1) + (((-(57593 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (279531 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 44`; spec_pass/nonlinear_ineqdata3q1h.hl:529. -/
def problem297 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(35429 / 200000 : ℝ)))) + ((((75667 / 500000 : ℝ) + ((2599 / 62500 : ℝ) + ((199 / 20000 : ℝ) + (2599 / 62500 : ℝ)))) * y1) + ((((2 : ℕ) : ℝ) * (((-(25827 / 250000 : ℝ)) + (25827 / 250000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((25827 / 250000 : ℝ) + (-(25827 / 250000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(25827 / 250000 : ℝ)) + (25827 / 250000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((25827 / 250000 : ℝ) + (-(25827 / 250000 : ℝ))) * y41)) + ((387477 / 500000 : ℝ) + ((-(677721 / 1000000 : ℝ)) + ((528759 / 500000 : ℝ) + (-(677721 / 1000000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 44`; spec_pass/nonlinear_ineqdata3q1h.hl:529. -/
def problem298 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(35429 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((75667 / 500000 : ℝ) * y1) + (((-(25827 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (387477 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 44`; spec_pass/nonlinear_ineqdata3q1h.hl:529. -/
def problem299 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(35429 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((2599 / 62500 : ℝ) * y1) + (((25827 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(677721 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 44`; spec_pass/nonlinear_ineqdata3q1h.hl:529. -/
def problem300 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(35429 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((199 / 20000 : ℝ) * y1) + (((-(25827 / 250000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (528759 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 44`; spec_pass/nonlinear_ineqdata3q1h.hl:529. -/
def problem301 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) , (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ))) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(35429 / 200000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((2599 / 62500 : ℝ) * y1) + (((25827 / 250000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(677721 / 1000000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 0 45`; spec_pass/nonlinear_ineqdata3q1h.hl:535. -/
def problem302 : Problem where
  arity := 5
  domain := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), (((2 : ℕ) : ℝ) , (y12 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y23 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y34 , (((2 : ℕ) : ℝ) * hminus))), (((2 : ℕ) : ℝ) , (y41 , (((2 : ℕ) : ℝ) * hminus)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y12 := x 1;
    let y23 := x 2;
    let y34 := x 3;
    let y41 := x 4;
    (((((2 : ℕ) : ℝ) * (Real.pi * (-(121189 / 1000000 : ℝ)))) + ((((6473 / 100000 : ℝ) + ((-(4063 / 250000 : ℝ)) + ((-(22099 / 1000000 : ℝ)) + (-(4063 / 250000 : ℝ))))) * y1) + ((((2 : ℕ) : ℝ) * (((-(84657 / 1000000 : ℝ)) + (84657 / 1000000 : ℝ)) * y12)) + ((((2 : ℕ) : ℝ) * (((84657 / 1000000 : ℝ) + (-(84657 / 1000000 : ℝ))) * y23)) + ((((2 : ℕ) : ℝ) * (((-(84657 / 1000000 : ℝ)) + (84657 / 1000000 : ℝ)) * y34)) + ((((2 : ℕ) : ℝ) * (((84657 / 1000000 : ℝ) + (-(84657 / 1000000 : ℝ))) * y41)) + ((741383 / 1000000 : ℝ) + ((-(22929 / 50000 : ℝ)) + ((455523 / 500000 : ℝ) + (-(22929 / 50000 : ℝ))))))))))) < ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 1 45`; spec_pass/nonlinear_ineqdata3q1h.hl:535. -/
def problem303 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))) , (y4 , (Prod.snd ((((2 : ℕ) : ℝ) * hminus) , (((2 : ℕ) : ℝ) * h0))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((2 : ℕ) : ℝ)) + ((((1 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(121189 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((6473 / 100000 : ℝ) * y1) + (((-(84657 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (741383 / 1000000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 2 45`; spec_pass/nonlinear_ineqdata3q1h.hl:535. -/
def problem304 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(121189 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4063 / 250000 : ℝ)) * y1) + (((84657 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(22929 / 50000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 3 45`; spec_pass/nonlinear_ineqdata3q1h.hl:535. -/
def problem305 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(121189 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(22099 / 1000000 : ℝ)) * y1) + (((-(84657 / 1000000 : ℝ)) * (y2 + (y3 + (y5 + y6)))) + (455523 / 500000 : ℝ)))))) > ((0 : ℕ) : ℝ))

/-- `OXLZLEZ 6346351218 4 45`; spec_pass/nonlinear_ineqdata3q1h.hl:535. -/
def problem306 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((Prod.fst ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))) , (y1 , (Prod.snd ((((2 : ℕ) : ℝ) * h0) , (((((2 : ℕ) : ℝ) * h0) + (((2 : ℕ) : ℝ) * hplus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y2 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y3 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))) , (y4 , (Prod.snd (((2 : ℕ) : ℝ) , ((((2 : ℕ) : ℝ) + (((2 : ℕ) : ℝ) * hminus)) / ((2 : ℕ) : ℝ)))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y5 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))))), ((Prod.fst (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus))) , (y6 , (Prod.snd (((2 : ℕ) : ℝ) , (((2 : ℕ) : ℝ) * hminus)))))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((gamma4fgcy y1) y2) y3) y4) y5) y6) lmfun) / ((1 : ℕ) : ℝ)) + ((((0 : ℕ) : ℝ) * ((((((beta_bump_force_y y1) y2) y3) y4) y5) y6)) + (((-(121189 / 1000000 : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) + (((-(4063 / 250000 : ℝ)) * y1) + (((84657 / 1000000 : ℝ) * (y2 + (y3 + (y5 + y6)))) + (-(22929 / 50000 : ℝ))))))) > ((0 : ℕ) : ℝ))

/-- `1965189142 34`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1588. -/
def problem307 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [((1 : ℝ) , (x1 , (63 / 50 : ℝ))), (((1 : ℕ) : ℝ) , (x2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x3 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((591 / 1000 : ℝ) - ((331 / 10000 : ℝ) * ((34 : ℕ) : ℝ))) + ((253 / 500 : ℝ) * ((((((lfun_y1 x1) x2) x3) x4) x5) x6))) < ((0 : ℕ) : ℝ))

/-- `1965189142 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1599. -/
def problem308 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [((1 : ℝ) , (x1 , (63 / 50 : ℝ))), ((3 : ℝ) , (x2 , (34 : ℝ))), (((1 : ℕ) : ℝ) , (x3 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((((2 : ℕ) : ℝ) * Real.pi) - (((2 : ℕ) : ℝ) * ((((((asnFnhk x1) x2) x3) x4) x5) x6))) > (((591 / 1000 : ℝ) - ((331 / 10000 : ℝ) * x2)) + ((253 / 500 : ℝ) * ((((((lfun_y1 x1) x2) x3) x4) x5) x6))))

/-- `8055810915`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1635. -/
def problem309 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , ((63 / 25 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x2 , ((4 : ℕ) : ℝ))), (((((2 : ℕ) : ℝ) * h0) ^ 2) , (x3 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((1 : ℕ) : ℝ) , (x4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((((((((acs_sqrt_x1_d4 x1) x2) x3) x4) x5) x6) - (Real.pi / ((6 : ℕ) : ℝ))) + (797 / 1000 : ℝ)) < ((((((arclength_x_123 x1) x2) x3) x4) x5) x6))

/-- `6096597438 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1651. -/
def problem310 : Problem where
  arity := 1
  domain := fun x ↦
    let h := x 0;
    inClosedIntervals [((1 : ℝ) , (h , (1 : ℝ)))]
  conclusion := fun x ↦
    let h := x 0;
    ((((591 / 1000 : ℝ) - ((331 / 10000 : ℝ) * ((64 : ℕ) : ℝ))) + (((253 / 500 : ℝ) * (lfun ((1 : ℕ) : ℝ))) + (1 : ℝ))) < ((0 : ℕ) : ℝ))

/-- `6096597438 b`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1662. -/
def problem311 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [((3 : ℝ) , (x1 , (64 : ℝ))), (((1 : ℕ) : ℝ) , (x2 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x3 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x4 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x5 , ((1 : ℕ) : ℝ))), (((1 : ℕ) : ℝ) , (x6 , ((1 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((((2 : ℕ) : ℝ) * Real.pi) - (((2 : ℕ) : ℝ) * ((((((asn797k x1) x2) x3) x4) x5) x6))) > (((591 / 1000 : ℝ) - ((331 / 10000 : ℝ) * x1)) + (((253 / 500 : ℝ) * (lfun ((1 : ℕ) : ℝ))) + (1 : ℝ))))

/-- `4717061266`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1699. -/
def problem312 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `JNTEFVP 1`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1756. -/
def problem313 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((4 : ℕ) : ℝ) , (x2 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((4 : ℕ) : ℝ) , (x3 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((4 : ℕ) : ℝ) , (x4 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((4 : ℕ) : ℝ) , (x5 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((8 : ℕ) : ℝ) , (x6 , ((((4 : ℕ) : ℝ) * h0) ^ 2)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((((((delta_x4 x1) x2) x3) x4) x5) x6) > ((0 : ℕ) : ℝ))

/-- `4652969746 1`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1776. -/
def problem314 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((21771 / 10000 : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (1 / 25 : ℝ))

/-- `4652969746 2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1793. -/
def problem315 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (21771 / 10000 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) - ((39 / 125 : ℝ) * (((((((dih_y y1) y2) y3) y4) y5) y6) - (((2 : ℕ) : ℝ) * (Real.pi / ((5 : ℕ) : ℝ)))))) > ((1 / 25 : ℝ) / ((5 : ℕ) : ℝ)))

/-- `2570626711`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1812. -/
def problem316 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2 : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) > (23 / 20 : ℝ))

/-- `3287695934`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1849. -/
def problem317 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((437 / 100 : ℝ) , (y1 , (((4 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y4 , (((4 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `8673686234 a`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1897. -/
def problem318 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(sqrt8 , (y1 , (3 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (207 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (207 / 100 : ℝ))), (sqrt8 , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (207 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (207 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((y2 + (y3 + (y5 + ((y6 - (799 / 100 : ℝ)) - ((77 / 20000 : ℝ) * ((((((delta_y y1) y2) y3) y4) y5) y6)))))) > ((11 / 4 : ℝ) * (((y1 + y4) / ((2 : ℕ) : ℝ)) - sqrt8)))

/-- `8673686234 b`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1915. -/
def problem319 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(sqrt8 , (y1 , (3 : ℝ))), ((207 / 100 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((3 : ℝ) , (y4 , (3 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((y2 + (y3 + (y5 + (y6 - (799 / 100 : ℝ))))) > ((11 / 4 : ℝ) * (y1 - sqrt8))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `8673686234 c`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1933. -/
def problem320 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(sqrt8 , (y1 , (3 : ℝ))), ((207 / 100 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (sqrt8 , (y4 , (3 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((y2 + (y3 + (y5 + (y6 - (799 / 100 : ℝ))))) > ((11 / 4 : ℝ) * (((y1 + y4) / ((2 : ℕ) : ℝ)) - sqrt8))) ∨ (((y2 + (y3 + (y5 + ((y6 - (799 / 100 : ℝ)) - ((77 / 20000 : ℝ) * ((((((delta_y y1) y2) y3) y4) y5) y6)))))) > ((11 / 4 : ℝ) * (((y1 + y4) / ((2 : ℕ) : ℝ)) - sqrt8))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `6170936724`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1952. -/
def problem321 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((3 : ℕ) : ℝ) , (y1 , ((3 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x delta_x1) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `7043724150 a reduced v2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:1990. -/
def problem322 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((118 / 25 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - ((781 / 125 : ℝ) / ((2 : ℕ) : ℝ)))) > (0 : ℝ))

/-- `6944699408 a reduced`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2023. -/
def problem323 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((243 / 250 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - ((1707 / 1000 : ℝ) / ((2 : ℕ) : ℝ)))) > (0 : ℝ))

/-- `6078657299`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2075. -/
def problem324 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((84 / 25 : ℝ) , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (39609 / 100 : ℝ); (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `8384429938`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2098. -/
def problem325 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (84 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (((delta_234_x ((((2 : ℕ) : ℝ) * h0) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((98 : ℕ) : ℝ)) ∨ (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `9893763499`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2119. -/
def problem326 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (84 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (39609 / 100 : ℝ); (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ ((((((((y_of_x (((delta_234_x ((((2 : ℕ) : ℝ) * h0) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((98 : ℕ) : ℝ))))

/-- `5429228381`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2142. -/
def problem327 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (84 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) > (-(7 / 100 : ℝ))) ∨ ((((((((y_of_x (((delta_234_x ((((2 : ℕ) : ℝ) * h0) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((98 : ℕ) : ℝ)))

/-- `3508342905`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2162. -/
def problem328 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (84 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((taum y1) y2) y3) y4) y5) y6) - (7 / 100 : ℝ)) + (((7573 / 10000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - (1433 / 1000 : ℝ))) > ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((((2 : ℕ) : ℝ) * h0) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((98 : ℕ) : ℝ)))

/-- `2327525027`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2185. -/
def problem329 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (84 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((0 : ℕ) : ℝ) < ((((((delta_y y1) y2) y3) y4) y5) y6)) ∨ ((((((((y_of_x (((delta_234_x ((((2 : ℕ) : ℝ) * h0) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((98 : ℕ) : ℝ)))

/-- `1611600345x`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2206. -/
def problem330 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((63 / 25 : ℝ) , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) > (((1 / 10 : ℝ) - (11 / 10000 : ℝ)) + (((23 / 200 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + ((27 / 200 : ℝ) * (y2 - ((2 : ℕ) : ℝ)))))) ∨ (y2 < y3))

/-- `2608321088x`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2225. -/
def problem331 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((63 / 25 : ℝ) , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((1 / 10 : ℝ) - (11 / 10000 : ℝ)) + (((23 / 200 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((27 / 200 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((7573 / 10000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - (1433 / 1000 : ℝ)))))) > ((0 : ℕ) : ℝ)) ∨ ((((((((dih_y y1) y2) y3) y4) y5) y6) > (1621 / 1000 : ℝ)) ∨ (y2 < y3)))

/-- `4240815464 a reduced`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2245. -/
def problem332 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((7573 / 10000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - ((1433 / 1000 : ℝ) / ((2 : ℕ) : ℝ)))) > (0 : ℝ))

/-- `4092227918`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2279. -/
def problem333 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , ((7 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x2 , ((7 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x3 , ((7 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x4 , ((7 : ℕ) : ℝ))), (((8 : ℕ) : ℝ) , (x5 , ((28 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x6 , ((7 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((0 : ℕ) : ℝ) < ((((((delta4_squared_x x1) x2) x3) x4) x5) x6)) ∨ (((0 : ℕ) : ℝ) < ((((((delta_x x1) x2) x3) x4) x5) x6)))

/-- `8425800388`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2298. -/
def problem334 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((39 / 10 : ℝ) , (y5 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (1709 / 500 : ℝ); (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `3253650737`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2320. -/
def problem335 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((38 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6)))

/-- `6723997360`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2339. -/
def problem336 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((81 / 20 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > ((501 / 1000 : ℝ) / ((2 : ℕ) : ℝ))))

/-- `1968758929`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2360. -/
def problem337 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((29 / 10 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > (21 / 100 : ℝ)))

/-- `6404645741`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2380. -/
def problem338 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((957 / 500 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > (31 / 200 : ℝ)))

/-- `2513405547`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2401. -/
def problem339 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((34079 / 5000 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > (79 / 250 : ℝ)))

/-- `8293089898`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2422. -/
def problem340 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y5 , (39 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < ((833 / 1000 : ℝ) * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > (-(13 / 500 : ℝ))))

/-- `3862621143 side`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2444. -/
def problem341 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y5 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - ((453 / 1000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) + ((777 / 1000 : ℝ) / ((2 : ℕ) : ℝ))) > (0 : ℝ))

/-- `3862621143 front`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2460. -/
def problem342 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((((2 : ℕ) : ℝ) * h0) , (y4 , (29 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + ((((tame_table_d 2) 1) - ((453 / 1000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) + (777 / 1000 : ℝ))) > (0 : ℝ))

/-- `3862621143 back`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2476. -/
def problem343 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (sqrt8 , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > ((tame_table_d 2) 1))

/-- `5691615370`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2524. -/
def problem344 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((3 : ℝ) , (y1 , (3 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((3 : ℝ) , (y4 , (3 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((y2 + (y3 + (y5 + y6))) > (1059 / 125 : ℝ)) ∨ ((y2 < y3) ∨ ((y2 < y5) ∨ ((y2 < y6) ∨ (y3 < y6))))))

/-- `5584033259`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2571. -/
def problem345 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((3 : ℕ) : ℝ) , (y1 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (309 / 125 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (309 / 125 : ℝ))), (((3 : ℕ) : ℝ) , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (309 / 125 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (309 / 125 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((y1 < ((4 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `9563139965 d`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2638. -/
def problem346 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((3 : ℕ) : ℝ) , (y4 , ((3 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (309 / 125 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (309 / 125 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + ((1 / 2 : ℝ) * ((((1059 / 125 : ℝ) / ((2 : ℕ) : ℝ)) - y5) - y6))) > ((467 / 1000 : ℝ) / ((2 : ℕ) : ℝ)))

/-- `9563139965 e`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2658. -/
def problem347 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((3 : ℕ) : ℝ) , (y4 , ((3 : ℕ) : ℝ))), ((2467 / 1000 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > ((467 / 1000 : ℝ) - (23 / 200 : ℝ)))

/-- `9563139965 f`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2677. -/
def problem348 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((3 : ℕ) : ℝ) , (y4 , ((3 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (23 / 200 : ℝ))

/-- `5735387903`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2710. -/
def problem349 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) > (213 / 250 : ℝ))

/-- `5490182221`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2722. -/
def problem350 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (1893 / 1000 : ℝ))

/-- `3296257235`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2736. -/
def problem351 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((313 / 500 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) - (77 / 100 : ℝ))) > (0 : ℝ))

/-- `8519146937`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2744. -/
def problem352 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - ((259 / 1000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) + (8 / 25 : ℝ)) > (0 : ℝ))

/-- `4667071578`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2752. -/
def problem353 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - ((507 / 1000 : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6))) + (181 / 250 : ℝ)) > (0 : ℝ))

/-- `1395142356`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2760. -/
def problem354 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((1 / 1000 : ℝ) - ((9 / 50 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))) - ((1 / 8 : ℝ) * (y4 + (y5 + (y6 - (6 : ℝ))))))) > (0 : ℝ))

/-- `7394240696`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2770. -/
def problem355 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((sol_y y1) y2) y3) y4) y5) y6) - (441 / 800 : ℝ)) - ((49 / 250 : ℝ) * (y4 + (y5 + (y6 - (6 : ℝ)))))) + ((19 / 50 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))) > (0 : ℝ))

/-- `7726998381`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2780. -/
def problem356 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((sol_y y1) y2) y3) y4) y5) y6)) + ((5513 / 10000 : ℝ) + (((202 / 625 : ℝ) * (y4 + (y5 + (y6 - (6 : ℝ))))) - ((151 / 1000 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))))) > (0 : ℝ))

/-- `4047599236`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2791. -/
def problem357 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih_y y1) y2) y3) y4) y5) y6) - (3077 / 2500 : ℝ)) + ((((3639 / 10000 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((47 / 200 : ℝ) * (y1 - (2 : ℝ)))) - ((137 / 200 : ℝ) * (y4 - (2 : ℝ))))) > (0 : ℝ))

/-- `3526497018`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2801. -/
def problem358 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + (((1231 / 1000 : ℝ) - ((19 / 125 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ))))))) + (((1 / 2 : ℝ) * (y1 - (2 : ℝ))) + ((773 / 1000 : ℝ) * (y4 - (2 : ℝ)))))) > (0 : ℝ))

/-- `5957966880`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2812. -/
def problem359 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((rhazim y1) y2) y3) y4) y5) y6) - (3077 / 2500 : ℝ)) + ((((3639 / 10000 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((3 / 5 : ℝ) * (y1 - (2 : ℝ)))) - ((137 / 200 : ℝ) * (y4 - (2 : ℝ))))) > (0 : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `3020140039`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2838. -/
def problem360 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dartX y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih_y y1) y2) y3) y4) y5) y6) - (1629 / 1000 : ℝ)) + (((201 / 500 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((63 / 200 : ℝ) * (y1 - (2 : ℝ))))) > (0 : ℝ))

/-- `9414951439`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2857. -/
def problem361 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dartY y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih_y y1) y2) y3) y4) y5) y6) - (191 / 100 : ℝ)) + (((229 / 500 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((171 / 500 : ℝ) * (y1 - (2 : ℝ))))) > (0 : ℝ))

/-- `9995621667`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2876. -/
def problem362 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart4_diag3 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih_y y1) y2) y3) y4) y5) y6) - (209 / 100 : ℝ)) + (((289 / 500 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((27 / 50 : ℝ) * (y1 - (2 : ℝ))))) > (0 : ℝ))

/-- `6988401556`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2898. -/
def problem363 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (103 / 1000 : ℝ))

/-- `8248508703`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2907. -/
def problem364 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((((taum y1) y2) y3) y4) y5) y6) - (1 / 10 : ℝ)) - ((53 / 200 : ℝ) * (y5 + (y6 - (4 : ℝ))))) - ((3 / 50 : ℝ) * (y4 - (63 / 25 : ℝ)))) - ((4 / 25 : ℝ) * (y1 - (2 : ℝ)))) - ((23 / 200 : ℝ) * (y2 + (y3 - (4 : ℝ))))) > (0 : ℝ))

/-- `3318775219`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2919. -/
def problem365 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih_y y1) y2) y3) y4) y5) y6) - (1629 / 1000 : ℝ)) + ((((207 / 500 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ)))))) - ((763 / 1000 : ℝ) * (y4 - (63 / 25 : ℝ)))) - ((63 / 200 : ℝ) * (y1 - (2 : ℝ))))) > (0 : ℝ))

/-- `9922699028`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2931. -/
def problem366 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + (((8147 / 5000 : ℝ) - ((2213 / 10000 : ℝ) * (y2 + (y3 + (y5 + (y6 - (8 : ℝ))))))) + (((913 / 1000 : ℝ) * (y4 - (63 / 25 : ℝ))) + ((91 / 125 : ℝ) * (y1 - (2 : ℝ)))))) > (0 : ℝ))

/-- `5000076558`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2943. -/
def problem367 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((dih2_y y1) y2) y3) y4) y5) y6) - (1083 / 1000 : ℝ)) + ((((1273 / 2000 : ℝ) * (y1 - (2 : ℝ))) - ((99 / 500 : ℝ) * (y2 - (2 : ℝ)))) + (((44 / 125 : ℝ) * (y3 - (2 : ℝ))) + ((((52 / 125 : ℝ) * (y4 - (63 / 25 : ℝ))) - ((33 / 50 : ℝ) * (y5 - (2 : ℝ)))) + ((71 / 1000 : ℝ) * (y6 - (2 : ℝ))))))) > (0 : ℝ))

/-- `9251360200`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2958. -/
def problem368 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((rhazim y1) y2) y3) y4) y5) y6) - (1629 / 1000 : ℝ)) - ((433 / 500 : ℝ) * (y1 - (2 : ℝ)))) + ((((761 / 2000 : ℝ) * (y2 + (y3 - (4 : ℝ)))) - ((841 / 1000 : ℝ) * (y4 - (63 / 25 : ℝ)))) + ((501 / 1000 : ℝ) * (y5 + (y6 - (4 : ℝ)))))) > (0 : ℝ))

/-- `9756015945`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2971. -/
def problem369 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((rhazim2 y1) y2) y3) y4) y5) y6) - (27 / 25 : ℝ)) + ((((3181 / 5000 : ℝ) * (y1 - (2 : ℝ))) - ((113 / 200 : ℝ) * (y2 - (2 : ℝ)))) + (((359 / 1000 : ℝ) * (y3 - (2 : ℝ))) + ((((52 / 125 : ℝ) * (y4 - (63 / 25 : ℝ))) - ((333 / 500 : ℝ) * (y5 - (2 : ℝ)))) + ((61 / 1000 : ℝ) * (y6 - (2 : ℝ))))))) > (0 : ℝ))

/-- `8082208587`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:2994. -/
def problem370 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_A y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (2759 / 10000 : ℝ))

/-- `5760733457`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3004. -/
def problem371 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_A y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (2141 / 2000 : ℝ)) - ((1 / 10 : ℝ) * (y1 - (2 : ℝ)))) + (((53 / 125 : ℝ) * (y2 - (2 : ℝ))) + ((((53 / 125 : ℝ) * (y3 - (2 : ℝ))) - ((297 / 500 : ℝ) * (y4 - (2 : ℝ)))) + (((31 / 250 : ℝ) * (y5 - (63 / 25 : ℝ))) + ((31 / 250 : ℝ) * (y6 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `2563100177`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3017. -/
def problem372 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_A y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((rhazim y1) y2) y3) y4) y5) y6) - (2137 / 2000 : ℝ)) - ((927 / 2000 : ℝ) * (y1 - (2 : ℝ)))) + (((53 / 125 : ℝ) * (y2 - (2 : ℝ))) + ((((53 / 125 : ℝ) * (y3 - (2 : ℝ))) - ((297 / 500 : ℝ) * (y4 - (2 : ℝ)))) + (((31 / 250 : ℝ) * (y5 - (63 / 25 : ℝ))) + ((31 / 250 : ℝ) * (y6 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `7931207804`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3032. -/
def problem373 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_A y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - (27 / 100 : ℝ)) + (((((((59 / 2000 : ℝ) * (y1 - (2 : ℝ))) - ((389 / 5000 : ℝ) * (y2 - (2 : ℝ)))) - ((389 / 5000 : ℝ) * (y3 - (2 : ℝ)))) - ((37 / 100 : ℝ) * (y4 - (2 : ℝ)))) - ((27 / 100 : ℝ) * (y5 - (63 / 25 : ℝ)))) - ((27 / 100 : ℝ) * (y6 - (63 / 25 : ℝ))))) > (0 : ℝ))

/-- `9225295803`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3055. -/
def problem374 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_small y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((17 / 5000 : ℝ) - ((83 / 500 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))) - ((11 / 50 : ℝ) * (y4 + (y5 + (y6 - (6 : ℝ))))))) > (0 : ℝ))

/-- `9291937879`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3066. -/
def problem375 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_small y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (123 / 100 : ℝ)) - ((47 / 200 : ℝ) * (y1 - (2 : ℝ)))) + ((((181 / 500 : ℝ) * (y2 + (y3 - (4 : ℝ)))) - ((347 / 500 : ℝ) * (y4 - (2 : ℝ)))) + ((13 / 50 : ℝ) * (y5 + (y6 - (4 : ℝ)))))) > (0 : ℝ))

/-- `7761782916`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3082. -/
def problem376 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_big y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((taum y1) y2) y3) y4) y5) y6) - (1 / 20 : ℝ)) - ((137 / 1000 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))) - ((17 / 100 : ℝ) * (y4 + (y5 + (y6 - (25 / 4 : ℝ)))))) > (0 : ℝ)) ∨ ((y4 + (y5 + y6)) < (25 / 4 : ℝ)))

/-- `6224332984`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3093. -/
def problem377 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_big y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((sol_y y1) y2) y3) y4) y5) y6) - (589 / 1000 : ℝ)) + (((39 / 100 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ))))) - ((47 / 200 : ℝ) * (y4 + (y5 + (y6 - (25 / 4 : ℝ))))))) > (0 : ℝ)) ∨ ((y4 + (y5 + y6)) < (25 / 4 : ℝ)))

/-- `5451229371`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3113. -/
def problem378 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((taum y1) y2) y3) y4) y5) y6) - (11 / 100 : ℝ)) - ((3533 / 25000 : ℝ) * (y1 + (((y2 + y3) / ((2 : ℕ) : ℝ)) - ((4 : ℕ) : ℝ))))) - ((19 / 50 : ℝ) * (y5 + (y6 - ((4 : ℕ) : ℝ))))) > ((0 : ℕ) : ℝ))

/-- `4840774900`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3124. -/
def problem379 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((taum y1) y2) y3) y4) y5) y6) - (527 / 5000 : ℝ)) - ((3533 / 25000 : ℝ) * (y1 + ((y2 / ((2 : ℕ) : ℝ)) + ((y3 / ((2 : ℕ) : ℝ)) - ((4 : ℕ) : ℝ)))))) - ((36499 / 100000 : ℝ) * (y5 + (y6 - ((4 : ℕ) : ℝ))))) > ((0 : ℕ) : ℝ))

/-- `1642527039`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3135. -/
def problem380 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - (16 / 125 : ℝ)) - ((53 / 1000 : ℝ) * ((y5 + (y6 - ((4 : ℕ) : ℝ))) - (((11 / 4 : ℝ) / ((2 : ℕ) : ℝ)) * (y4 - sqrt8))))) > ((0 : ℕ) : ℝ))

/-- `7863247282`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3145. -/
def problem381 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((((taum y1) y2) y3) y4) y5) y6) - ((53 / 1000 : ℝ) * ((y5 + (y6 - ((4 : ℕ) : ℝ))) - (((11 / 4 : ℝ) / ((2 : ℕ) : ℝ)) * (y4 - sqrt8))))) - (3 / 25 : ℝ)) - ((3533 / 25000 : ℝ) * (y1 + ((y2 / ((2 : ℕ) : ℝ)) + ((y3 / ((2 : ℕ) : ℝ)) - ((4 : ℕ) : ℝ)))))) - ((41 / 125 : ℝ) * (y5 + (y6 - ((4 : ℕ) : ℝ))))) > ((0 : ℕ) : ℝ))

/-- `7718591733`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3156. -/
def problem382 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih2_y y1) y2) y3) y4) y5) y6) - (191 / 200 : ℝ)) - ((589 / 2500 : ℝ) * (y2 - ((2 : ℕ) : ℝ)))) + (((8 / 25 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + ((((99 / 125 : ℝ) * (y1 - ((2 : ℕ) : ℝ))) - ((707 / 1000 : ℝ) * (y5 - ((2 : ℕ) : ℝ)))) + (((211 / 2500 : ℝ) * (y6 - ((2 : ℕ) : ℝ))) + ((821 / 1000 : ℝ) * (y4 - sqrt8)))))) > ((0 : ℕ) : ℝ))

/-- `3566713650`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3168. -/
def problem383 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + ((1911 / 1000 : ℝ) + ((((101 / 100 : ℝ) * (y1 - ((2 : ℕ) : ℝ))) - ((71 / 250 : ℝ) * (y2 + (y3 + (y5 + (y6 - ((8 : ℕ) : ℝ))))))) + ((107 / 100 : ℝ) * (y4 - sqrt8))))) > ((0 : ℕ) : ℝ))

/-- `1085358243`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3179. -/
def problem384 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (1903 / 1000 : ℝ)) - ((2 / 5 : ℝ) * (y1 - ((2 : ℕ) : ℝ)))) + (((6211 / 12500 : ℝ) * (y2 + (y3 + (y5 + (y6 - ((8 : ℕ) : ℝ)))))) - (y4 - sqrt8))) > ((0 : ℕ) : ℝ))

/-- `9229542852`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3203. -/
def problem385 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_mini y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (123 / 100 : ℝ)) - ((2357 / 10000 : ℝ) * (y1 - (2 : ℝ)))) + ((((2493 / 10000 : ℝ) * (y2 + (y3 - (4 : ℝ)))) - ((341 / 500 : ℝ) * (y4 - (2 : ℝ)))) + ((607 / 2000 : ℝ) * (y5 + (y6 - (4 : ℝ)))))) > (0 : ℝ))

/-- `1550635295`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3215. -/
def problem386 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_mini y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + ((154 / 125 : ℝ) + ((((261 / 1000 : ℝ) * (y1 - (2 : ℝ))) - ((203 / 1000 : ℝ) * (y2 + (y3 - (4 : ℝ))))) + (((193 / 250 : ℝ) * (y4 - (2 : ℝ))) - ((191 / 1000 : ℝ) * (y5 + (y6 - (4 : ℝ)))))))) > (0 : ℝ))

/-- `4491491732`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3227. -/
def problem387 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_mini y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((1 / 1250 : ℝ) - ((1631 / 10000 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ)))))) - ((2127 / 10000 : ℝ) * (y4 + (y5 + (y6 - (6 : ℝ))))))) > (0 : ℝ))

/-- `8282573160`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3245. -/
def problem388 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((((taum y1) y2) y3) y4) y5) y6) - (1413 / 10000 : ℝ)) - ((107 / 500 : ℝ) * (y1 - (109 / 50 : ℝ)))) - ((1259 / 10000 : ℝ) * (y2 + (y3 - (4 : ℝ))))) - ((67 / 1000 : ℝ) * (y4 - (63 / 25 : ℝ)))) - ((241 / 1000 : ℝ) * (y5 + (y6 - (4 : ℝ))))) > (0 : ℝ))

/-- `8611785756`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3265. -/
def problem389 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_big_200_218 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((sol_y y1) y2) y3) y4) y5) y6) - (589 / 1000 : ℝ)) + (((6 / 25 : ℝ) * (y1 + (y2 + (y3 - (6 : ℝ))))) - ((4 / 25 : ℝ) * (y4 + (y5 + (y6 - (25 / 4 : ℝ))))))) > (0 : ℝ)) ∨ ((y4 + (y5 + y6)) < (25 / 4 : ℝ)))

/-- `181212899 0`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3334. -/
def problem390 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexffA y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y2 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y3 - (2 : ℝ))) - ((149 / 200 : ℝ) * (y4 - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y5 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y6 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `181212899 1`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3335. -/
def problem391 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexfA y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y3 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y2 - (2 : ℝ))) - ((149 / 200 : ℝ) * (y4 - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y6 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y5 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `181212899 2`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3336. -/
def problem392 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexf4 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y2 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y3 - (2 : ℝ))) - ((149 / 200 : ℝ) * (sqrt8 - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y5 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y6 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `181212899 3`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3337. -/
def problem393 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexff4 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y3 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y2 - (2 : ℝ))) - ((149 / 200 : ℝ) * (sqrt8 - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y6 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y5 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `181212899 4`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3338. -/
def problem394 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexf5 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y2 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y3 - (2 : ℝ))) - ((149 / 200 : ℝ) * ((63 / 25 : ℝ) - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y5 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y6 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `181212899 5`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3339. -/
def problem395 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apexff5 y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((dih_y y1) y2) y3) y4) y5) y6) - (181 / 125 : ℝ)) - ((133 / 500 : ℝ) * (y1 - (2 : ℝ)))) + (((59 / 200 : ℝ) * (y3 - (2 : ℝ))) + ((((57 / 100 : ℝ) * (y2 - (2 : ℝ))) - ((149 / 200 : ℝ) * ((63 / 25 : ℝ) - (63 / 25 : ℝ)))) + (((67 / 250 : ℝ) * (y6 - (2 : ℝ))) + ((77 / 200 : ℝ) * (y5 - (63 / 25 : ℝ))))))) > (0 : ℝ))

/-- `2151506422`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3461. -/
def problem396 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((12777 / 10000 : ℝ) + (((281 / 1000 : ℝ) * (y1 - (109 / 50 : ℝ))) + (((-(69591 / 250000 : ℝ)) * (y2 - ((2 : ℕ) : ℝ))) + (((-(69591 / 250000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((7117 / 10000 : ℝ) * (y4 - ((2 : ℕ) : ℝ))) + (((-(1073 / 3125 : ℝ)) * (y5 - ((2 : ℕ) : ℝ))) + ((-(1073 / 3125 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `6836427086`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3466. -/
def problem397 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(127799 / 100000 : ℝ)) + (((-(356217 / 1000000 : ℝ)) * (y1 - (109 / 50 : ℝ))) + (((114733 / 500000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((114733 / 500000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(949067 / 1000000 : ℝ)) * (y4 - ((2 : ℕ) : ℝ))) + (((86363 / 500000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((86363 / 500000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `3636849632`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3471. -/
def problem398 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((taum y1) y2) y3) y4) y5) y6)) > ((69 / 2000 : ℝ) + (((37109 / 200000 : ℝ) * (y1 - (109 / 50 : ℝ))) + (((193139 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((193139 / 1000000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((42537 / 250000 : ℝ) * (y4 - ((2 : ℕ) : ℝ))) + (((2639 / 20000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((2639 / 20000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `5298513205`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3476. -/
def problem399 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((237 / 200 : ℝ) + (((-(302913 / 1000000 : ℝ)) * (y1 - (109 / 50 : ℝ))) + (((214849 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(6551 / 40000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(443449 / 1000000 : ℝ)) * (y4 - ((2 : ℕ) : ℝ))) + (((16841 / 25000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(78633 / 250000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `7743522046`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3481. -/
def problem400 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((-(2373 / 2000 : ℝ)) + (((10379 / 50000 : ℝ) * (y1 - (109 / 50 : ℝ))) + (((-(236153 / 1000000 : ℝ)) * (y2 - ((2 : ℕ) : ℝ))) + (((3543 / 25000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((131917 / 500000 : ℝ) * (y4 - ((2 : ℕ) : ℝ))) + (((-(771203 / 1000000 : ℝ)) * (y5 - ((2 : ℕ) : ℝ))) + ((114323 / 2500000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `8657368829`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3488. -/
def problem401 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_small_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((1277 / 1000 : ℝ) + (((136649 / 500000 : ℝ) * (y1 - (109 / 50 : ℝ))) + (((-(273853 / 1000000 : ℝ)) * (y2 - ((2 : ℕ) : ℝ))) + (((-(273853 / 1000000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((354409 / 500000 : ℝ) * (y4 - ((2 : ℕ) : ℝ))) + (((-(78497 / 250000 : ℝ)) * (y5 - ((2 : ℕ) : ℝ))) + ((-(78497 / 250000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `6619134733`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3493. -/
def problem402 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_small_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(127799 / 100000 : ℝ)) + (((-(219501 / 500000 : ℝ)) * (y1 - (109 / 50 : ℝ))) + (((114733 / 500000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((114733 / 500000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(771733 / 1000000 : ℝ)) * (y4 - ((2 : ℕ) : ℝ))) + (((208429 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((208429 / 1000000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `1284543870`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3498. -/
def problem403 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_small_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((237 / 200 : ℝ) + (((-(186131 / 500000 : ℝ)) * (y1 - (109 / 50 : ℝ))) + (((214849 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(6551 / 40000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(73377 / 250000 : ℝ)) * (y4 - ((2 : ℕ) : ℝ))) + (((164043 / 250000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(267157 / 1000000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `4041673283`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3503. -/
def problem404 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_small_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((-(1483 / 1250 : ℝ)) + (((10379 / 50000 : ℝ) * (y1 - (109 / 50 : ℝ))) + (((-(236153 / 1000000 : ℝ)) * (y2 - ((2 : ℕ) : ℝ))) + (((3543 / 25000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((263109 / 1000000 : ℝ) * (y4 - ((2 : ℕ) : ℝ))) + (((-(737003 / 1000000 : ℝ)) * (y5 - ((2 : ℕ) : ℝ))) + ((12047 / 100000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `3872614111`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3508. -/
def problem405 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_w y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(771 / 500 : ℝ)) + (((-(362519 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((298691 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((57413 / 200000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(184157 / 200000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((190917 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((54783 / 250000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `3139693500`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3513. -/
def problem406 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(771 / 500 : ℝ)) + (((-(346773 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((300751 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((300751 / 1000000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(702567 / 1000000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((86363 / 500000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((172727 / 1000000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `4841020453`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3518. -/
def problem407 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_Hll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(771 / 500 : ℝ)) + (((-(490439 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((509 / 1600 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((8117 / 25000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(740079 / 1000000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((44717 / 250000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((205819 / 1000000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `9925287433`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3523. -/
def problem408 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_Hll_w y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((1 : ℕ) : ℝ)) * ((((((dih_y y1) y2) y3) y4) y5) y6)) > ((-(771 / 500 : ℝ)) + (((-(490439 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((321849 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((80239 / 250000 : ℝ) * (y3 - ((2 : ℕ) : ℝ))) + (((-(50451 / 50000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((240709 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((218081 / 1000000 : ℝ) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `7409690040`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3528. -/
def problem409 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_w y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((5247 / 5000 : ℝ) + (((-(297823 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((6729 / 31250 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(792439 / 10000000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(211337 / 500000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((80927 / 125000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(207561 / 1000000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `4002562507`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3533. -/
def problem410 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((5247 / 5000 : ℝ) + (((-(29013 / 100000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((6729 / 31250 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(715511 / 10000000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(267157 / 1000000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((650269 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(147599 / 500000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `5835568093`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3538. -/
def problem411 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_Hll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((5247 / 5000 : ℝ) + (((-(404131 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((212119 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(402827 / 10000000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(149523 / 500000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((643273 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(133059 / 500000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `1894886027`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3543. -/
def problem412 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_Hll_w y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((1 : ℕ) : ℝ) * ((((((dih2_y y1) y2) y3) y4) y5) y6)) > ((5247 / 5000 : ℝ) + (((-(401543 / 1000000 : ℝ)) * (y1 - (59 / 25 : ℝ))) + (((207551 / 1000000 : ℝ) * (y2 - ((2 : ℕ) : ℝ))) + (((-(294227 / 10000000 : ℝ)) * (y3 - ((2 : ℕ) : ℝ))) + (((-(247477 / 500000 : ℝ)) * (y4 - (9 / 4 : ℝ))) + (((605453 / 1000000 : ℝ) * (y5 - ((2 : ℕ) : ℝ))) + ((-(31277 / 200000 : ℝ)) * (y6 - ((2 : ℕ) : ℝ))))))))))

/-- `4750199435`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3583. -/
def problem413 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih2_y y1) y2) y3) y4) y5) y6)) + (31 / 10000 : ℝ)) > ((-(54173 / 50000 : ℝ)) + (((144397 / 500000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(292829 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y2)) + (((36457 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y3)) + (((87199 / 250000 : ℝ) * ((-(63 / 25 : ℝ)) + y4)) + (((-(381301 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(112679 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `8384511215`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3608. -/
def problem414 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (3 / 2000 : ℝ)) > ((456593 / 500000 : ℝ) + (((-(24393 / 62500 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y1)) + (((23179 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((32961 / 200000 : ℝ) * ((-(63 / 25 : ℝ)) + y3)) + (((-(271329 / 1000000 : ℝ)) * ((-(282843 / 100000 : ℝ)) + y4)) + (((584817 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(85109 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `7819193535`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3632. -/
def problem415 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_lw y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (11 / 10000 : ℝ)) > ((116613 / 100000 : ℝ) + (((-(37097 / 125000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y1)) + (((41787 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(121651 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(14423 / 40000 : ℝ)) * ((-(9 / 4 : ℝ)) + y4)) + (((127241 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(73789 / 250000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `6987934000`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3657. -/
def problem416 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_w y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (21 / 5000 : ℝ)) > ((476341 / 500000 : ℝ) + (((-(268837 / 1000000 : ℝ)) * ((-(59 / 25 : ℝ)) + y1)) + (((130607 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(168729 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(207941 / 2500000 : ℝ)) * ((-(63 / 25 : ℝ)) + y4)) + (((72519 / 125000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((164153 / 2500000 : ℝ) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `7291663656`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3675. -/
def problem417 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (9 / 10000 : ℝ)) > ((947391 / 1000000 : ℝ) + (((-(637397 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y1)) + (((120003 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(50407 / 500000 : ℝ)) * ((-(23 / 10 : ℝ)) + y3)) + (((-(75739 / 250000 : ℝ)) * ((-(53 / 20 : ℝ)) + y4)) + (((547359 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(31549 / 200000 : ℝ)) * ((-(11 / 5 : ℝ)) + y6)))))))))

/-- `2390583444`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3693. -/
def problem418 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_std3_mini y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih_y y1) y2) y3) y4) y5) y6) + (3 / 2500 : ℝ)) > ((108627 / 100000 : ℝ) + (((159149 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(6203 / 31250 : ℝ)) * ((-(21 / 10 : ℝ)) + y2)) + (((-(99653 / 500000 : ℝ)) * ((-(21 / 10 : ℝ)) + y3)) + (((590083 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y4)) + (((-(888111 / 10000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y5)) + ((-(440923 / 5000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `9641946727`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3733. -/
def problem419 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat_l y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (71 / 10000 : ℝ)) > ((49181 / 50000 : ℝ) + (((-(132047 / 500000 : ℝ)) * ((-(109 / 50 : ℝ)) + y1)) + (((37327 / 250000 : ℝ) * ((-(109 / 50 : ℝ)) + y2)) + (((-(312683 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(35349 / 125000 : ℝ)) * ((-(53 / 20 : ℝ)) + y4)) + (((36347 / 62500 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((143669 / 1000000 : ℝ) * ((-(23 / 10 : ℝ)) + y6)))))))))

/-- `4222324842`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3759. -/
def problem420 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lll_xww y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih_y y1) y2) y3) y4) y5) y6) + (71 / 10000 : ℝ)) > ((109969 / 100000 : ℝ) + (((29269 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(80269 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(75849 / 500000 : ℝ)) * ((-(107 / 50 : ℝ)) + y3)) + (((30657 / 50000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y4)) + (((-(236149 / 1000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y5)) + ((-(242043 / 1000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `5756588587`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3785. -/
def problem421 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lll_wxx y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (1 / 400 : ℝ)) > ((116613 / 100000 : ℝ) + (((-(37097 / 125000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y1)) + (((41787 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(196313 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(14423 / 40000 : ℝ)) * ((-(9 / 4 : ℝ)) + y4)) + (((652861 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(218063 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `3425739813`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3801. -/
def problem422 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + (11 / 10000 : ℝ)) > ((-(167609 / 100000 : ℝ)) + (((-(253161 / 500000 : ℝ)) * ((-(109 / 50 : ℝ)) + y1)) + (((8483 / 40000 : ℝ) * ((-(21 / 10 : ℝ)) + y2)) + (((230669 / 1000000 : ℝ) * ((-(21 / 10 : ℝ)) + y3)) + (((-(128579 / 100000 : ℝ)) * ((-(63 / 25 : ℝ)) + y4)) + (((249199 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((38709 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `7316455966`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3818. -/
def problem423 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lll_wxx y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (1 / 200 : ℝ)) > ((20401 / 20000 : ℝ) + (((-(128247 / 500000 : ℝ)) * ((-(109 / 50 : ℝ)) + y1)) + (((121497 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(128247 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(116869 / 10000000 : ℝ)) * ((-(63 / 25 : ℝ)) + y4)) + (((598233 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((23459 / 1250000 : ℝ) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `6410081357`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3834. -/
def problem424 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lll_wxx y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih3_y y1) y2) y3) y4) y5) y6)) + (87 / 10000 : ℝ)) > ((-(14827 / 12500 : ℝ)) + (((436647 / 1000000 : ℝ) * ((-(109 / 50 : ℝ)) + y1)) + (((16129 / 500000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(289629 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((397053 / 1000000 : ℝ) * ((-(63 / 25 : ℝ)) + y4)) + (((-(210289 / 10000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(683341 / 1000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `2923748598`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3850. -/
def problem425 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih_y y1) y2) y3) y4) y5) y6)) + (83 / 10000 : ℝ)) > ((-(16239 / 12500 : ℝ)) + (((-(284457 / 1000000 : ℝ)) * ((-(109 / 50 : ℝ)) + y1)) + (((168677 / 500000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((186287 / 1000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y3)) + (((-(322691 / 500000 : ℝ)) * ((-(9 / 4 : ℝ)) + y4)) + (((367671 / 1000000 : ℝ) * ((-(63 / 25 : ℝ)) + y5)) + ((536051 / 10000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `4306175952`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3866. -/
def problem426 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((dart_mll_n y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (7 / 2000 : ℝ)) > ((26259 / 25000 : ℝ) + (((-(111089 / 500000 : ℝ)) * ((-(109 / 50 : ℝ)) + y1)) + (((33157 / 250000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(54821 / 250000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((563427 / 100000000 : ℝ) * ((-(9 / 4 : ℝ)) + y4)) + (((7387 / 12500 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(385787 / 5000000 : ℝ)) * ((-(63 / 25 : ℝ)) + y6)))))))))

/-- `2763799127`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3882. -/
def problem427 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih3_y y1) y2) y3) y4) y5) y6)) + (19 / 2500 : ℝ)) > ((-(956317 / 1000000 : ℝ)) + (((104781 / 250000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(376961 / 5000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(252307 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y3)) + (((1 / 2 : ℝ) * ((-(282843 / 100000 : ℝ)) + y4)) + (((-(123041 / 500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(788717 / 1000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `5943578801`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3898. -/
def problem428 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_sup_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (47 / 10000 : ℝ)) > ((29267 / 31250 : ℝ) + (((-(636113 / 1000000 : ℝ)) * ((-(21 / 10 : ℝ)) + y1)) + (((140759 / 1000000 : ℝ) * ((-(21 / 10 : ℝ)) + y2)) + (((-(385867 / 5000000 : ℝ)) * ((-(23 / 10 : ℝ)) + y3)) + (((-(32267 / 25000 : ℝ)) * ((-(282843 / 100000 : ℝ)) + y4)) + (((18479 / 31250 : ℝ) * ((-(21 / 10 : ℝ)) + y5)) + ((-(20871 / 400000 : ℝ)) * ((-(21 / 10 : ℝ)) + y6)))))))))

/-- `1836408787`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3924. -/
def problem429 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lhh y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih_y y1) y2) y3) y4) y5) y6) + (3 / 2500 : ℝ)) > ((25333 / 25000 : ℝ) + (((29723 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(189503 / 500000 : ℝ)) * ((-(109 / 50 : ℝ)) + y2)) + (((-(379441 / 1000000 : ℝ)) * ((-(109 / 50 : ℝ)) + y3)) + (((145919 / 250000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y4)) + (((-(46177 / 250000 : ℝ)) * ((-(9 / 4 : ℝ)) + y5)) + ((-(18471 / 100000 : ℝ)) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `1248932983`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3940. -/
def problem430 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_lhh y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih2_y y1) y2) y3) y4) y5) y6)) + (59 / 10000 : ℝ)) > ((-(133909 / 100000 : ℝ)) + (((724529 / 10000000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y1)) + (((-(60853 / 125000 : ℝ)) * ((-(109 / 50 : ℝ)) + y2)) + (((317329 / 1000000 : ℝ) * ((-(109 / 50 : ℝ)) + y3)) + (((-(479451 / 100000000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y4)) + (((-(751179 / 1000000 : ℝ)) * ((-(9 / 4 : ℝ)) + y5)) + ((350857 / 1000000 : ℝ) * ((-(9 / 4 : ℝ)) + y6)))))))))

/-- `6725783616`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3958. -/
def problem431 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih3_y y1) y2) y3) y4) y5) y6) + (23 / 5000 : ℝ)) > ((88473 / 100000 : ℝ) + (((-(221973 / 500000 : ℝ)) * ((-(59 / 25 : ℝ)) + y1)) + (((-(244711 / 1000000 : ℝ)) * ((-(21 / 10 : ℝ)) + y2)) + (((25699 / 125000 : ℝ) * ((-(21 / 10 : ℝ)) + y3)) + (((-(369563 / 500000 : ℝ)) * ((-(51 / 20 : ℝ)) + y4)) + (((-(63599 / 500000 : ℝ)) * ((-(21 / 10 : ℝ)) + y5)) + ((30791 / 50000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y6)))))))))

/-- `9185711902`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3974. -/
def problem432 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((-((((((dih3_y y1) y2) y3) y4) y5) y6)) + (29 / 2500 : ℝ)) > ((-(130119 / 100000 : ℝ)) + (((78583 / 200000 : ℝ) * ((-(59 / 25 : ℝ)) + y1)) + (((142563 / 1000000 : ℝ) * ((-(21 / 10 : ℝ)) + y2)) + (((-(258747 / 1000000 : ℝ)) * ((-(21 / 10 : ℝ)) + y3)) + (((6517 / 15625 : ℝ) * ((-(49 / 20 : ℝ)) + y4)) + (((-(151691 / 2500000 : ℝ)) * ((-((2 : ℕ) : ℝ)) + y5)) + ((-(318983 / 500000 : ℝ)) * ((-(49 / 20 : ℝ)) + y6)))))))))

/-- `6284721194`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:3990. -/
def problem433 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_std3_hll y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (11 / 10000 : ℝ)) > ((957661 / 1000000 : ℝ) + (((-(125253 / 500000 : ℝ)) * ((-(59 / 25 : ℝ)) + y1)) + (((72557 / 500000 : ℝ) * ((-(21 / 10 : ℝ)) + y2)) + (((-(4292 / 78125 : ℝ)) * ((-(21 / 10 : ℝ)) + y3)) + (((-(76889 / 2000000 : ℝ)) * ((-(49 / 20 : ℝ)) + y4)) + (((211 / 400 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((118819 / 1000000 : ℝ) * ((-(49 / 20 : ℝ)) + y6)))))))))

/-- `3137600529`; sources/architecture/repo/text_formalization/nonlinear/ineq.hl:4006. -/
def problem434 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals ((((((apex_flat_h y1) y2) y3) y4) y5) y6)
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((dih2_y y1) y2) y3) y4) y5) y6) + (21 / 5000 : ℝ)) > ((434087 / 500000 : ℝ) + (((-(350953 / 500000 : ℝ)) * ((-(9 / 4 : ℝ)) + y1)) + (((68257 / 500000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y2)) + (((-(209239 / 1000000 : ℝ)) * ((-(109 / 50 : ℝ)) + y3)) + (((-(493373 / 1000000 : ℝ)) * ((-(53 / 20 : ℝ)) + y4)) + (((107477 / 200000 : ℝ) * ((-((2 : ℕ) : ℝ)) + y5)) + ((23459 / 1250000 : ℝ) * ((-(11 / 5 : ℝ)) + y6)))))))))

/-- `1834976363`; spec_pass/nonlinear_main_estimate_ineq.hl:61. -/
def problem435 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (x1 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (x2 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (x3 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (x4 , (1553 / 100 : ℝ))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (x5 , (((4 : ℕ) : ℝ) ^ 2))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (x6 , (((4 : ℕ) : ℝ) ^ 2)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((((((num1 x1) x2) x3) x4) x5) x6) > ((0 : ℕ) : ℝ)) ∨ ((((((((num1 x1) x2) x3) x4) x5) x6) < ((0 : ℕ) : ℝ)) ∨ (((((((dnum1 x1) x2) x3) x4) x5) x6) < ((0 : ℕ) : ℝ))))

/-- `4828966562`; spec_pass/nonlinear_main_estimate_ineq.hl:80. -/
def problem436 : Problem where
  arity := 6
  domain := fun x ↦
    let a2 := x 0;
    let b2 := x 1;
    let c2 := x 2;
    let e1 := x 3;
    let e2 := x 4;
    let e3 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (e1 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (e2 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (e3 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (a2 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (b2 , ((301 / 100 : ℝ) ^ 2))), (((119 / 50 : ℝ) ^ 2) , (c2 , (16 : ℝ)))]
  conclusion := fun x ↦
    let a2 := x 0;
    let b2 := x 1;
    let c2 := x 2;
    let e1 := x 3;
    let e2 := x 4;
    let e3 := x 5;
    (((((((num1 e1) e2) e3) a2) b2) c2) > ((0 : ℕ) : ℝ))

/-- `6843920790`; spec_pass/nonlinear_main_estimate_ineq.hl:100. -/
def problem437 : Problem where
  arity := 6
  domain := fun x ↦
    let a2 := x 0;
    let b2 := x 1;
    let c2 := x 2;
    let e1 := x 3;
    let e2 := x 4;
    let e3 := x 5;
    inClosedIntervals [(((1 : ℕ) : ℝ) , (e1 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (e2 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((1 : ℕ) : ℝ) , (e3 , (((1 : ℕ) : ℝ) + (sol0 / Real.pi)))), (((((2 : ℕ) : ℝ) / h0) ^ 2) , (a2 , ((301 / 100 : ℝ) ^ 2))), (((119 / 50 : ℝ) ^ 2) , (b2 , (1553 / 100 : ℝ))), (((119 / 50 : ℝ) ^ 2) , (c2 , (1553 / 100 : ℝ)))]
  conclusion := fun x ↦
    let a2 := x 0;
    let b2 := x 1;
    let c2 := x 2;
    let e1 := x 3;
    let e2 := x 4;
    let e3 := x 5;
    (((((((num1 e1) e2) e3) a2) b2) c2) > ((0 : ℕ) : ℝ))

/-- `1117202051`; spec_pass/nonlinear_main_estimate_ineq.hl:137. -/
def problem438 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (2 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `4559601669`; spec_pass/nonlinear_main_estimate_ineq.hl:155. -/
def problem439 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y3 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `4559601669b`; spec_pass/nonlinear_main_estimate_ineq.hl:173. -/
def problem440 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `2485876245a`; spec_pass/nonlinear_main_estimate_ineq.hl:194. -/
def problem441 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), ((3 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * (63 / 25 : ℝ)))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `2485876245b`; spec_pass/nonlinear_main_estimate_ineq.hl:214. -/
def problem442 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y5 , (((2 : ℕ) : ℝ) * (63 / 25 : ℝ)))), (((2 : ℕ) : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta4_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `7175074394`; spec_pass/nonlinear_main_estimate_ineq.hl:237. -/
def problem443 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (55093 / 500000 : ℝ); ((((((((delta_y y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ ((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6)))))

/-- `4887115291`; spec_pass/nonlinear_main_estimate_ineq.hl:269. -/
def problem444 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((7 / 4 : ℝ) < ((((((dih_y y1) y2) y3) y4) y5) y6))

/-- `6789182745`; spec_pass/nonlinear_main_estimate_ineq.hl:288. -/
def problem445 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (1109 / 1000 : ℝ))

/-- `7796879304`; spec_pass/nonlinear_main_estimate_ineq.hl:308. -/
def problem446 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta_y y1) y2) y3) y4) y5) y6) > ((80 : ℕ) : ℝ)) ∨ ((((((((y_of_x tau_residual_x) y1) y2) y3) y4) y5) y6) > ((3 / 250 : ℝ) + (((7 / 100 : ℝ) * ((63 / 25 : ℝ) - y1)) + ((1 / 100 : ℝ) * ((((63 / 25 : ℝ) * ((2 : ℕ) : ℝ)) - y2) - y3)))))))

/-- `2314572187`; spec_pass/nonlinear_main_estimate_ineq.hl:330. -/
def problem447 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) > (((((((y_of_x taud_x) y1) y2) y3) y4) y5) y6)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((80 : ℕ) : ℝ)))

/-- `1347067436`; spec_pass/nonlinear_main_estimate_ineq.hl:352. -/
def problem448 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (3237 / 1000 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x taud_D1_num_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_D1_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_D2_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_x) y1) y2) y3) y4) y5) y6) > (3 / 25 : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((20 : ℕ) : ℝ))))))

/-- `3078028960`; spec_pass/nonlinear_main_estimate_ineq.hl:376. -/
def problem449 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x delta_x1) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)))

/-- `6601228004`; spec_pass/nonlinear_main_estimate_ineq.hl:397. -/
def problem450 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (3237 / 1000 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x taud_D2_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta_y y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `3665919985`; spec_pass/nonlinear_main_estimate_ineq.hl:419. -/
def problem451 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (541 / 1000 : ℝ))

/-- `7903347843`; spec_pass/nonlinear_main_estimate_ineq.hl:436. -/
def problem452 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (3 / 25 : ℝ))) > (77 / 125 : ℝ))

/-- `5546286427`; spec_pass/nonlinear_main_estimate_ineq.hl:461. -/
def problem453 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let d := ((0 : ℕ) : ℝ); (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x d) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (3 / 25 : ℝ))) > (77 / 125 : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > d)))

/-- `7997589055`; spec_pass/nonlinear_main_estimate_ineq.hl:487. -/
def problem454 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0))) > (77 / 125 : ℝ))

/-- `2320951108`; spec_pass/nonlinear_main_estimate_ineq.hl:513. -/
def problem455 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (53 / 1000 : ℝ))) > (77 / 125 : ℝ))

/-- `5429238960`; spec_pass/nonlinear_main_estimate_ineq.hl:539. -/
def problem456 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ ((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)) > (77 / 125 : ℝ)))

/-- `2565248885`; spec_pass/nonlinear_main_estimate_ineq.hl:563. -/
def problem457 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let d := ((0 : ℕ) : ℝ); (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x d) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0))) > (77 / 125 : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > d)))

/-- `5708641738`; spec_pass/nonlinear_main_estimate_ineq.hl:589. -/
def problem458 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let d := ((20 : ℕ) : ℝ); (((((((((taum y1) y2) y3) y4) y5) y6) + (53 / 1000 : ℝ)) > (77 / 125 : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > d)))

/-- `1948775510`; spec_pass/nonlinear_main_estimate_ineq.hl:618. -/
def problem459 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((y_of_x (((mud_135_x_v1 (((2 : ℕ) : ℝ) * h0)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6))) > (77 / 125 : ℝ)) ∨ (((((((((y_of_x (((delta_135_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((20 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))))

/-- `1586903463`; spec_pass/nonlinear_main_estimate_ineq.hl:644. -/
def problem460 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_135_x ((20 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((3 / 250 : ℝ) + ((1 / 100 : ℝ) * ((((63 / 25 : ℝ) * ((2 : ℕ) : ℝ)) - y1) - y3))) * (447 / 100 : ℝ)) + ((0 : ℕ) : ℝ)))) > (77 / 125 : ℝ)) ∨ (((((((((y_of_x (((delta_135_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)))))

/-- `8875146520`; spec_pass/nonlinear_main_estimate_ineq.hl:673. -/
def problem461 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_135_x ((20 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((3 / 250 : ℝ) + ((1 / 100 : ℝ) * ((((63 / 25 : ℝ) * ((2 : ℕ) : ℝ)) - y1) - y3))) * (447 / 100 : ℝ)) + (((((((y_of_x (((mud_126_x_v1 (((2 : ℕ) : ℝ) * h0)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6)))) > (77 / 125 : ℝ)) ∨ (((((((((y_of_x (((delta_135_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((20 : ℕ) : ℝ))))

/-- `1008824382`; spec_pass/nonlinear_main_estimate_ineq.hl:702. -/
def problem462 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (3237 / 1000 : ℝ))), ((301 / 100 : ℝ) , (y6 , (3237 / 1000 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((141 / 200 : ℝ) * (((((((y_of_x (((flat_term2_135_x ((20 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6)) + ((((3 / 250 : ℝ) + ((1 / 100 : ℝ) * ((((63 / 25 : ℝ) * ((2 : ℕ) : ℝ)) - y1) - y3))) * (447 / 100 : ℝ)) + (((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6)))) > (77 / 125 : ℝ)) ∨ (((((((((y_of_x (((delta_135_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((20 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x (((4 : ℕ) : ℝ) * (h0 * h0))) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))))

/-- `6459846571`; spec_pass/nonlinear_main_estimate_ineq.hl:735. -/
def problem463 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (113 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((y4 < (783 / 200 : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `7439076204`; spec_pass/nonlinear_main_estimate_ineq.hl:755. -/
def problem464 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x delta_x4) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)))

/-- `6877738680`; spec_pass/nonlinear_main_estimate_ineq.hl:795. -/
def problem465 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x taud_D1_num_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_D1_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_D2_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x taud_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((15 : ℕ) : ℝ))))))

/-- `9692636487`; spec_pass/nonlinear_main_estimate_ineq.hl:818. -/
def problem466 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((((y_of_x taud_D2_num_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) > ((15 : ℕ) : ℝ)))

/-- `7823243247`; spec_pass/nonlinear_main_estimate_ineq.hl:841. -/
def problem467 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , (3969 / 625 : ℝ))), (((4 : ℕ) : ℝ) , (x2 , (3969 / 625 : ℝ))), (((4 : ℕ) : ℝ) , (x3 , (3969 / 625 : ℝ))), ((9 : ℝ) , (x4 , (1916 / 125 : ℝ))), ((9 : ℝ) , (x5 , (1916 / 125 : ℝ))), ((9 : ℝ) , (x6 , (1916 / 125 : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((0 : ℕ) : ℝ) < ((((((delta_x x1) x2) x3) x4) x5) x6)) ∨ (((((((eulerA_x x1) x2) x3) x4) x5) x6) < ((0 : ℕ) : ℝ)))

/-- `5744538693`; spec_pass/nonlinear_main_estimate_ineq.hl:863. -/
def problem468 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [(((4 : ℕ) : ℝ) , (x1 , ((8 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x2 , ((7 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x3 , ((7 : ℕ) : ℝ))), (((8 : ℕ) : ℝ) , (x4 , ((28 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x5 , ((7 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x6 , ((7 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((0 : ℕ) : ℝ) < ((((((delta4_squared_x x1) x2) x3) x4) x5) x6)) ∨ (((0 : ℕ) : ℝ) < ((((((delta_x x1) x2) x3) x4) x5) x6)))

/-- `7550003505 0 0 0`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem469 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((y_of_x (((flat_term2_135_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ (y5 < y6)))))))

/-- `7550003505 0 0 1`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem470 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((0 : ℕ) : ℝ)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (False ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 0 0 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem471 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 0 0 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem472 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 0 0 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem473 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_126_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 0 1 1`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem474 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (False ∨ (False ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 0 1 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem475 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (False ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (False ∨ False))))))

/-- `7550003505 0 1 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem476 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (False ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 0 1 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem477 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (False ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 0 2 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem478 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 0 2 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem479 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ False))))))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `7550003505 0 2 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem480 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 0 3 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem481 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 0 3 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem482 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 0 4 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem483 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((((((y_of_x (((flat_term2_234_x ((0 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) + ((((0 : ℕ) : ℝ) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((63 / 25 : ℝ) ^ 2)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 1 1 1`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem484 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (False ∨ (False ∨ ((y6 < y4) ∨ (y5 < y6)))))))

/-- `7550003505 1 1 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem485 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (False ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 1 1 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem486 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (False ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 1 1 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem487 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (False ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 1 2 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem488 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 1 2 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem489 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 1 2 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem490 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 1 3 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem491 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 1 3 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem492 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 1 4 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem493 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((0 : ℕ) : ℝ) + ((((0 : ℕ) : ℝ) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (False ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 2 2 2`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem494 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((mud_135_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((y6 < y4) ∨ (y5 < y6)))))))

/-- `7550003505 2 2 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem495 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 2 2 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem496 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((mud_126_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 2 3 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem497 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 2 3 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem498 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ False))))))

/-- `7550003505 2 4 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem499 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((mud_234_x_v1 ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((0 : ℕ) : ℝ) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ (((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((100 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 3 3 3`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem500 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((((mudLs_234_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((((((y_of_x (((((mudLs_135_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ (y5 < y6)))))))

/-- `7550003505 3 3 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem501 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((((mudLs_234_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((((((((y_of_x (((((mudLs_126_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ False))))))

/-- `7550003505 3 4 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem502 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + (((((((((y_of_x (((((mudLs_234_x ((4 : ℕ) : ℝ)) ((10 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)) ((2 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) - sol0) + ((((0 : ℕ) : ℝ) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((16 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((100 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ (False ∨ (y5 < y6)))))))

/-- `7550003505 4 4 4`; spec_pass/nonlinear_main_estimate_ineq.hl:959. -/
def problem503 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), ((301 / 100 : ℝ) , (y6 , (783 / 200 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((((0 : ℕ) : ℝ) - sol0) + ((((0 : ℕ) : ℝ) - sol0) + (((0 : ℕ) : ℝ) - sol0)))) > (89 / 125 : ℝ)) ∨ (((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_234_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_126_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)) ∨ ((((((((y_of_x (((delta_135_x ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ)) ((4 : ℕ) : ℝ))) y1) y2) y3) y4) y5) y6) > ((16 : ℕ) : ℝ))) ∨ ((y6 < y4) ∨ (y5 < y6)))))))

/-- `6762190381`; spec_pass/nonlinear_main_estimate_ineq.hl:969. -/
def problem504 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta_y y1) y2) y3) y4) y5) y6) < ((200 : ℕ) : ℝ)) ∨ (((((((taum y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)))

/-- `8346775862`; spec_pass/nonlinear_main_estimate_ineq.hl:985. -/
def problem505 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((delta_y y1) y2) y3) y4) y5) y6) > ((200 : ℕ) : ℝ)) ∨ ((((((((y_of_x delta_x4) y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `8631418063`; spec_pass/nonlinear_main_estimate_ineq.hl:1001. -/
def problem506 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x delta_x4) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `4821120729`; spec_pass/nonlinear_main_estimate_ineq.hl:1016. -/
def problem507 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), ((2 : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((y_of_x eulerA_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `5202826650 a`; spec_pass/nonlinear_main_estimate_ineq.hl:1032. -/
def problem508 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((63 / 25 : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (783 / 200 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((y_of_x tau_residual_x) y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `6184614449`; spec_pass/nonlinear_main_estimate_ineq.hl:1068. -/
def problem509 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y2 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y3 , (((2 : ℕ) : ℝ) * h0))), ((33 / 10 : ℝ) , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (((2 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `2073661826`; spec_pass/nonlinear_main_estimate_ineq.hl:1084. -/
def problem510 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((71 / 20 : ℝ) , (y4 , (((4 : ℕ) : ℝ) * h0))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `1348932091`; spec_pass/nonlinear_main_estimate_ineq.hl:1100. -/
def problem511 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y5 , (33 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (7 / 5 : ℝ))

/-- `1348932091 delta`; spec_pass/nonlinear_main_estimate_ineq.hl:1116. -/
def problem512 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y5 , (33 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `5557288534`; spec_pass/nonlinear_main_estimate_ineq.hl:1132. -/
def problem513 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), ((301 / 100 : ℝ) , (y5 , (33 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (17 / 10 : ℝ))

/-- `5557288534 delta`; spec_pass/nonlinear_main_estimate_ineq.hl:1148. -/
def problem514 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), ((301 / 100 : ℝ) , (y5 , (33 / 10 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `9368433105`; spec_pass/nonlinear_main_estimate_ineq.hl:1165. -/
def problem515 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (71 / 20 : ℝ))), ((((2 : ℕ) : ℝ) * h0) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta4_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `8405387449`; spec_pass/nonlinear_main_estimate_ineq.hl:1181. -/
def problem516 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (71 / 20 : ℝ))), ((((2 : ℕ) : ℝ) * h0) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (let tan2lower := (193 / 50 : ℝ); (((((4 : ℕ) : ℝ) * ((((((x1_delta_y y1) y2) y3) y4) y5) y6)) < (tan2lower * ((((((delta4_squared_y y1) y2) y3) y4) y5) y6))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))))

/-- `5550839403`; spec_pass/nonlinear_main_estimate_ineq.hl:1203. -/
def problem517 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), ((301 / 100 : ℝ) , (y5 , (71 / 20 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((dih_y y1) y2) y3) y4) y5) y6) < (2 : ℝ))

/-- `5550839403 delta`; spec_pass/nonlinear_main_estimate_ineq.hl:1220. -/
def problem518 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (301 / 100 : ℝ))), ((301 / 100 : ℝ) , (y5 , (71 / 20 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (((2 : ℕ) : ℝ) * h0)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

/-- `4680581274 1x`; spec_pass/nonlinear_main_estimate_ineq.hl:1304. -/
def problem519 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [((4 : ℝ) , (x1 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), ((4 : ℝ) , (x2 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), ((4 : ℝ) , (x3 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((301 / 100 : ℝ) ^ 2) , (x4 , ((1583 / 500 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x5 , ((4 : ℕ) : ℝ))), (((4 : ℕ) : ℝ) , (x6 , ((4 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    ((((((((taud_x x1) x2) x3) x4) x5) x6) > (-(7 / 250 : ℝ))) ∨ (((((((delta_x x1) x2) x3) x4) x5) x6) < ((10 : ℕ) : ℝ)))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- `4680581274 2x`; spec_pass/nonlinear_main_estimate_ineq.hl:1320. -/
def problem520 : Problem where
  arity := 6
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    inClosedIntervals [((4 : ℝ) , (x1 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), ((4 : ℝ) , (x2 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), ((4 : ℝ) , (x3 , ((((2 : ℕ) : ℝ) * h0) ^ 2))), (((301 / 100 : ℝ) ^ 2) , (x4 , ((1583 / 500 : ℝ) ^ 2))), (((301 / 100 : ℝ) ^ 2) , (x5 , ((301 / 100 : ℝ) ^ 2))), (((4 : ℕ) : ℝ) , (x6 , ((4 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    (((((((taum_x x1) x2) x3) x4) x5) x6) > (541 / 1000 : ℝ))

/-- `4680581274 delta issue-cayleytr0`; spec_pass/nonlinear_main_estimate_ineq.hl:1390. -/
def problem521 : Problem where
  arity := 9
  domain := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    let x7 := x 6;
    let x8 := x 7;
    let x9 := x 8;
    inClosedIntervals [((4 : ℝ) , (x1 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x2 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x3 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x4 , ((1583 / 500 : ℝ) * (1583 / 500 : ℝ)))), ((4 : ℝ) , (x5 , (4 : ℝ))), ((4 : ℝ) , (x6 , (4 : ℝ))), ((4 : ℝ) , (x7 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x8 , (4 : ℝ))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x9 , ((301 / 100 : ℝ) * (301 / 100 : ℝ))))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x2 := x 1;
    let x3 := x 2;
    let x4 := x 3;
    let x5 := x 4;
    let x6 := x 5;
    let x7 := x 6;
    let x8 := x 7;
    let x9 := x 8;
    ((((((((((((cayleytr x3) x2) x1) x7) x4) x5) x8) x6) x9) ((0 : ℕ) : ℝ)) < ((0 : ℕ) : ℝ)) ∨ (((((10 : ℕ) : ℝ) + (((((((delta_x x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ)))) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta_x4 x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ))) < ((0 : ℕ) : ℝ))))

/-- `4680581274 delta issue-cayleytr`; spec_pass/nonlinear_main_estimate_ineq.hl:1423. -/
def problem522 : Problem where
  arity := 10
  domain := fun x ↦
    let x1 := x 0;
    let x10 := x 1;
    let x2 := x 2;
    let x3 := x 3;
    let x4 := x 4;
    let x5 := x 5;
    let x6 := x 6;
    let x7 := x 7;
    let x8 := x 8;
    let x9 := x 9;
    inClosedIntervals [((4 : ℝ) , (x1 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x2 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x3 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x4 , ((1583 / 500 : ℝ) * (1583 / 500 : ℝ)))), ((4 : ℝ) , (x5 , (4 : ℝ))), ((4 : ℝ) , (x6 , (4 : ℝ))), ((4 : ℝ) , (x7 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x8 , (4 : ℝ))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x9 , ((301 / 100 : ℝ) * (301 / 100 : ℝ)))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x10 , ((301 / 100 : ℝ) * (301 / 100 : ℝ))))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x10 := x 1;
    let x2 := x 2;
    let x3 := x 3;
    let x4 := x 4;
    let x5 := x 5;
    let x6 := x 6;
    let x7 := x 7;
    let x8 := x 8;
    let x9 := x 9;
    ((((0 : ℕ) : ℝ) < ((((2 : ℕ) : ℝ) * ((((ups_x x2) x3) x4) * x10)) + ((((((((((cayleytr x3) x2) x1) x7) x4) x5) x8) x6) x9) ((0 : ℕ) : ℝ)))) ∨ (((((10 : ℕ) : ℝ) + (((((((delta_x x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ)))) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta_x4 x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ))) < ((0 : ℕ) : ℝ))))

/-- `4680581274 delta issue-cayleyR`; spec_pass/nonlinear_main_estimate_ineq.hl:1456. -/
def problem523 : Problem where
  arity := 10
  domain := fun x ↦
    let x1 := x 0;
    let x10 := x 1;
    let x2 := x 2;
    let x3 := x 3;
    let x4 := x 4;
    let x5 := x 5;
    let x6 := x 6;
    let x7 := x 7;
    let x8 := x 8;
    let x9 := x 9;
    inClosedIntervals [((4 : ℝ) , (x1 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x2 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x3 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x4 , ((1583 / 500 : ℝ) * (1583 / 500 : ℝ)))), ((4 : ℝ) , (x5 , (4 : ℝ))), ((4 : ℝ) , (x6 , (4 : ℝ))), ((4 : ℝ) , (x7 , ((2 : ℝ) * ((63 / 50 : ℝ) * ((2 : ℝ) * (63 / 50 : ℝ)))))), ((4 : ℝ) , (x8 , (4 : ℝ))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x9 , ((301 / 100 : ℝ) * (301 / 100 : ℝ)))), (((301 / 100 : ℝ) * (301 / 100 : ℝ)) , (x10 , ((301 / 100 : ℝ) * (301 / 100 : ℝ))))]
  conclusion := fun x ↦
    let x1 := x 0;
    let x10 := x 1;
    let x2 := x 2;
    let x3 := x 3;
    let x4 := x 4;
    let x5 := x 5;
    let x6 := x 6;
    let x7 := x 7;
    let x8 := x 8;
    let x9 := x 9;
    ((((0 : ℕ) : ℝ) < ((((((((((cayleyR x3) x2) x1) x7) x4) x5) x8) x6) x9) x10)) ∨ (((((10 : ℕ) : ℝ) + (((((((delta_x x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ)))) < ((0 : ℕ) : ℝ)) ∨ ((((((((delta_x4 x1) x2) x3) x4) x5) x6) * (-((1 : ℕ) : ℝ))) < ((0 : ℕ) : ℝ))))

/-- `4680581274 delta top issue`; spec_pass/nonlinear_main_estimate_ineq.hl:1491. -/
def problem524 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((1583 / 500 : ℝ) , (y1 , ((4 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y2 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , ((2 : ℕ) : ℝ))), ((1583 / 500 : ℝ) , (y4 , ((4 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `2171548893`; spec_pass/nonlinear_main_estimate_ineq.hl:1513. -/
def problem525 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y2 , (301 / 100 : ℝ))), ((181 / 50 : ℝ) , (y3 , ((6 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y5 , (301 / 100 : ℝ))), ((181 / 50 : ℝ) , (y6 , ((6 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `2468307358`; spec_pass/nonlinear_main_estimate_ineq.hl:1531. -/
def problem526 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y4 , (181 / 50 : ℝ))), ((301 / 100 : ℝ) , (y5 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (513 / 2000 : ℝ))

/-- `3603097872`; spec_pass/nonlinear_main_estimate_ineq.hl:1739. -/
def problem527 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) - ((1 / 10 : ℝ) * ((301 / 100 : ℝ) - y4))) > (11 / 100 : ℝ)) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `5405130650`; spec_pass/nonlinear_main_estimate_ineq.hl:1761. -/
def problem528 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , (301 / 100 : ℝ))), ((63 / 25 : ℝ) , (y5 , sqrt8)), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((((taum y1) y2) y3) y4) y5) y6) + ((1 / 10 : ℝ) * ((301 / 100 : ℝ) - y4))) > ((477 / 1000 : ℝ) - (11 / 100 : ℝ))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `5026777310a`; spec_pass/nonlinear_main_estimate_ineq.hl:1784. -/
def problem529 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (sqrt8 , (y4 , (301 / 100 : ℝ))), (sqrt8 , (y5 , (301 / 100 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (63 / 25 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) > (((tame_table_d 4) 1) - (((2 : ℕ) : ℝ) * (11 / 100 : ℝ)))) ∨ (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ)))

/-- `7881254908`; spec_pass/nonlinear_main_estimate_ineq.hl:1803. -/
def problem530 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (63 / 25 : ℝ))), (sqrt8 , (y5 , (301 / 100 : ℝ))), (sqrt8 , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > ((87 / 125 : ℝ) - (((2 : ℕ) : ℝ) * (11 / 100 : ℝ))))

/-- `4010906068`; spec_pass/nonlinear_main_estimate_ineq.hl:1825. -/
def problem531 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y4 , (301 / 100 : ℝ))), ((63 / 25 : ℝ) , (y5 , (301 / 100 : ℝ))), ((63 / 25 : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (119 / 250 : ℝ))

/-- `6833979866`; spec_pass/nonlinear_main_estimate_ineq.hl:1843. -/
def problem532 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y5 , (301 / 100 : ℝ))), ((63 / 25 : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (2759 / 10000 : ℝ))

/-- `5541487347`; spec_pass/nonlinear_main_estimate_ineq.hl:1861. -/
def problem533 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y6 , sqrt8))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > (103 / 1000 : ℝ))

/-- `OMKYNLT 3336871894`; spec_pass/nonlinear_main_estimate_ineq.hl:1878. -/
def problem534 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [((2 : ℝ) , (y1 , (63 / 25 : ℝ))), ((2 : ℝ) , (y2 , (63 / 25 : ℝ))), ((2 : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y5 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y6 , ((2 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) >= (0 : ℝ))

/-- `8495326405`; spec_pass/nonlinear_main_estimate_ineq.hl:1895. -/
def problem535 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , ((2 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y2 , ((2 : ℕ) : ℝ))), ((301 / 100 : ℝ) , (y3 , ((6 : ℕ) : ℝ))), (((2 : ℕ) : ℝ) , (y4 , ((2 : ℕ) : ℝ))), ((((2 : ℕ) : ℝ) * h0) , (y5 , (((2 : ℕ) : ℝ) * h0))), ((301 / 100 : ℝ) , (y6 , ((6 : ℕ) : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) < ((0 : ℕ) : ℝ))

/-- `9096461391`; spec_pass/nonlinear_main_estimate_ineq.hl:1914. -/
def problem536 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), ((63 / 25 : ℝ) , (y5 , (301 / 100 : ℝ))), ((301 / 100 : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    ((((((((taum y1) y2) y3) y4) y5) y6) + ((3 / 25 : ℝ) * (y1 - ((2 : ℕ) : ℝ)))) > (403 / 1000 : ℝ))

/-- `2445657182`; spec_pass/nonlinear_main_estimate_ineq.hl:1932. -/
def problem537 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), ((301 / 100 : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((taum y1) y2) y3) y4) y5) y6) > ((11 / 100 : ℝ) + ((3 / 25 : ℝ) * (y1 - ((2 : ℕ) : ℝ)))))

/-- `2125338128`; spec_pass/nonlinear_main_estimate_ineq.hl:1949. -/
def problem538 : Problem where
  arity := 6
  domain := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    inClosedIntervals [(((2 : ℕ) : ℝ) , (y1 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y2 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y3 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y4 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y5 , (63 / 25 : ℝ))), (((2 : ℕ) : ℝ) , (y6 , (301 / 100 : ℝ)))]
  conclusion := fun x ↦
    let y1 := x 0;
    let y2 := x 1;
    let y3 := x 2;
    let y4 := x 3;
    let y5 := x 4;
    let y6 := x 5;
    (((((((delta_y y1) y2) y3) y4) y5) y6) > ((0 : ℕ) : ℝ))

end KeplerMission.Nonlinear

end

/-! Generated from official Flyspeck revision 1ce0353008eba83d3c76ae9a25c3c242e4802d53.
Generator: missions/kepler-conjecture/spec_pass/nonlinear_translate.py.
Each record contains its actual real formula; source identifiers are documentation only.
The propositions are specification targets. No validity proof is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace KeplerMission.Nonlinear

/-- Exact `packing` source selector, 81 obligations; repeated formulas retain their meaning. -/
def packingCatalog : List Problem :=
  [problem000, problem001, problem002, problem003, problem004, problem005, problem006, problem007, problem008, problem009, problem010, problem011, problem012, problem013, problem014, problem015, problem016, problem017, problem018, problem019, problem020, problem021, problem022, problem023, problem024, problem025, problem026, problem027, problem028, problem029, problem030, problem031, problem032, problem033, problem034, problem035, problem036, problem037, problem038, problem039, problem040, problem041, problem042, problem043, problem044, problem045, problem046, problem047, problem048, problem049, problem050, problem051, problem052, problem053, problem054, problem055, problem056, problem057, problem058, problem059, problem060, problem061, problem062, problem063, problem064, problem065, problem066, problem067, problem068, problem069, problem070, problem071, problem072, problem073, problem074, problem075, problem076, problem307, problem308, problem310, problem311]

/-- Exact `ox3q1h` source selector, 230 obligations; repeated formulas retain their meaning. -/
def ox3q1hCatalog : List Problem :=
  [problem077, problem078, problem079, problem080, problem081, problem082, problem083, problem084, problem085, problem086, problem087, problem088, problem089, problem090, problem091, problem092, problem093, problem094, problem095, problem096, problem097, problem098, problem099, problem100, problem101, problem102, problem103, problem104, problem105, problem106, problem107, problem108, problem109, problem110, problem111, problem112, problem113, problem114, problem115, problem116, problem117, problem118, problem119, problem120, problem121, problem122, problem123, problem124, problem125, problem126, problem127, problem128, problem129, problem130, problem131, problem132, problem133, problem134, problem135, problem136, problem137, problem138, problem139, problem140, problem141, problem142, problem143, problem144, problem145, problem146, problem147, problem148, problem149, problem150, problem151, problem152, problem153, problem154, problem155, problem156, problem157, problem158, problem159, problem160, problem161, problem162, problem163, problem164, problem165, problem166, problem167, problem168, problem169, problem170, problem171, problem172, problem173, problem174, problem175, problem176, problem177, problem178, problem179, problem180, problem181, problem182, problem183, problem184, problem185, problem186, problem187, problem188, problem189, problem190, problem191, problem192, problem193, problem194, problem195, problem196, problem197, problem198, problem199, problem200, problem201, problem202, problem203, problem204, problem205, problem206, problem207, problem208, problem209, problem210, problem211, problem212, problem213, problem214, problem215, problem216, problem217, problem218, problem219, problem220, problem221, problem222, problem223, problem224, problem225, problem226, problem227, problem228, problem229, problem230, problem231, problem232, problem233, problem234, problem235, problem236, problem237, problem238, problem239, problem240, problem241, problem242, problem243, problem244, problem245, problem246, problem247, problem248, problem249, problem250, problem251, problem252, problem253, problem254, problem255, problem256, problem257, problem258, problem259, problem260, problem261, problem262, problem263, problem264, problem265, problem266, problem267, problem268, problem269, problem270, problem271, problem272, problem273, problem274, problem275, problem276, problem277, problem278, problem279, problem280, problem281, problem282, problem283, problem284, problem285, problem286, problem287, problem288, problem289, problem290, problem291, problem292, problem293, problem294, problem295, problem296, problem297, problem298, problem299, problem300, problem301, problem302, problem303, problem304, problem305, problem306]

/-- Exact `terminal` source selector, 109 obligations; repeated formulas retain their meaning. -/
def terminalCatalog : List Problem :=
  [problem312, problem344, problem346, problem347, problem348, problem435, problem436, problem437, problem438, problem439, problem440, problem441, problem442, problem443, problem444, problem445, problem446, problem447, problem448, problem449, problem450, problem451, problem452, problem453, problem454, problem455, problem456, problem457, problem458, problem459, problem460, problem461, problem462, problem463, problem464, problem465, problem466, problem467, problem468, problem469, problem470, problem471, problem472, problem473, problem474, problem475, problem476, problem477, problem478, problem479, problem480, problem481, problem482, problem483, problem484, problem485, problem486, problem487, problem488, problem489, problem490, problem491, problem492, problem493, problem494, problem495, problem496, problem497, problem498, problem499, problem500, problem501, problem502, problem503, problem504, problem505, problem506, problem507, problem508, problem509, problem510, problem511, problem512, problem513, problem514, problem515, problem516, problem517, problem518, problem519, problem520, problem521, problem522, problem523, problem524, problem525, problem526, problem527, problem528, problem529, problem530, problem531, problem532, problem533, problem534, problem535, problem536, problem537, problem538]

/-- Exact `lp` source selector, 127 obligations; repeated formulas retain their meaning. -/
def linearRelaxationCatalog : List Problem :=
  [problem313, problem314, problem315, problem316, problem317, problem318, problem319, problem320, problem321, problem322, problem323, problem324, problem325, problem326, problem327, problem328, problem329, problem330, problem331, problem332, problem333, problem334, problem335, problem336, problem337, problem338, problem339, problem340, problem341, problem342, problem343, problem344, problem345, problem346, problem347, problem348, problem349, problem350, problem351, problem352, problem353, problem354, problem355, problem356, problem357, problem358, problem359, problem360, problem361, problem362, problem363, problem364, problem365, problem366, problem367, problem368, problem369, problem370, problem371, problem372, problem373, problem374, problem375, problem376, problem377, problem378, problem379, problem380, problem381, problem382, problem383, problem384, problem385, problem386, problem387, problem388, problem389, problem390, problem391, problem392, problem393, problem394, problem395, problem396, problem397, problem398, problem399, problem400, problem401, problem402, problem403, problem404, problem405, problem406, problem407, problem408, problem409, problem410, problem411, problem412, problem413, problem414, problem415, problem416, problem417, problem418, problem419, problem420, problem421, problem422, problem423, problem424, problem425, problem426, problem427, problem428, problem429, problem430, problem431, problem432, problem433, problem434, problem504, problem505, problem506, problem507, problem509]

/-- Exact `packA` source selector, 5 obligations; repeated formulas retain their meaning. -/
def packingSeparationCatalog : List Problem :=
  [problem307, problem308, problem309, problem310, problem311]

/-- Exact `kcblrqc` source selector, 28 obligations; repeated formulas retain their meaning. -/
def tamenessCatalog : List Problem :=
  [problem313, problem314, problem315, problem316, problem317, problem324, problem325, problem326, problem327, problem328, problem329, problem330, problem331, problem334, problem335, problem336, problem337, problem338, problem339, problem340, problem341, problem349, problem350, problem351, problem352, problem353, problem363, problem509]

/-- The six nonlinear components of the_main_statement.hl:55–59. -/
def catalog : List Problem :=
  packingCatalog ++
  ox3q1hCatalog ++
  terminalCatalog ++
  linearRelaxationCatalog ++
  packingSeparationCatalog ++
  tamenessCatalog

/-- Mathematical validity of the complete fixed source catalog. -/
def CatalogValid : Prop := ∀ p ∈ catalog, p.Valid

/-- Certificate completion does not follow from generic soundness: the fixed source data
also require accepted certificates and pointwise encoding bridges. -/
def CatalogCertificateCompletion (check : Checker) : Prop :=
  check.Sound ∧ CatalogCertified catalog check

/-- Conditional assembly from a sound checker and complete certificates. -/
theorem catalogValid_of_certificates (check : Checker)
    (h : CatalogCertificateCompletion check) : CatalogValid :=
  catalog_valid_of_certified catalog check h.1 h.2

end KeplerMission.Nonlinear

end


