-- Prove2me | Definitions.Def_AT260939824_RectangularCone
-- name    : AT260939824_RectangularCone
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:52:41.074728+00:00
-- url     : https://prove2.me/theorems/fb0f16f7-34d6-45e6-b6a0-ff5a80d28c5b
-- title:
--   Normalized rectangular coordinates for a controlled cone filling
-- statement:
--   Let $d\in\mathbb N$, $o,\ell\in\mathbb R^d$, and assume $\ell_i>0$ for every $i$. The rectangular domain and its normalized transverse coordinate are
--   $$R(o,\ell)=\{z:|z_i-o_i|\le\ell_i/2\ \forall i\},\qquad
--   N(z)_i=\frac{2(z_i-o_i)}{\ell_i}.$$
--   Thus $N(z)$ belongs to the maximum-norm unit ball. For real $A,\delta,r$, define $u(r)=\operatorname{clamp}_{[0,1]}((r-A)/\delta)$; with the total convention $u(r)=0$ when $\delta=0$; hence $u(A)=0$ for every $\delta$. Given a controlled contraction $H$ to $p$ in a metric space and a boundary path family $F$ from $p$ to $q$ with finite path-time and transverse bounds, define
--   $$V(r,z)=\operatorname{ConeFill}_{H,F}(N(z),u(r)).$$
--   Its left face is $V(A,z)=p$. The longitudinal coordinate is normalized independently of all transverse side lengths.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularCone.lean, selected declaration lines 21-22, 24-33, 60, 74-75, 86-89, 128-131; SHA-256 f4fc60f3dfeadfb1966c2ceb4e1276ae593021456f13f8bc2347f91349bc27cc. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Physical coordinate estimates for the rectangular cone

This transports the checked radial extension to a literal rectangle.
The first physical coordinate is normalized independently of the
transverse coordinates. The resulting bounds are divided by the
corresponding side lengths, as in Lemma 5.2.
-/

namespace AbelianTargets

open scoped unitInterval NNReal

noncomputable section

variable {d : ℕ}

abbrev RectanglePoint (o ℓ : Fin d → ℝ) :=
  {z : Fin d → ℝ // ∀ i, |z i-o i| ≤ ℓ i/2}

def normalizeRectangle (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i)
    (z : RectanglePoint o ℓ) : ConeBall (Fin d → ℝ) :=
  ⟨fun i => 2*(z.val i-o i)/ℓ i, by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (hℓ i)]
    norm_num
    apply (div_le_iff₀ (hℓ i)).mpr
    have := z.property i
    linarith⟩





def physicalFirstParameter (A δ : ℝ) (r : ℝ) : I := clampInterval ((r-A)/δ)



@[simp] theorem physicalFirstParameter_left (A δ : ℝ) : physicalFirstParameter A δ A = 0 := by
  simp [physicalFirstParameter]



namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)

def rectangularValue (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ)
    (r : ℝ) (z : RectanglePoint o ℓ) : Z :=
  H.coneValue F (normalizeRectangle o ℓ hℓ z) (physicalFirstParameter A δ r)







@[simp] theorem rectangularValue_left (F : BoundaryPathFamily (E := Fin d → ℝ) p q S B)
    (o ℓ : Fin d → ℝ) (hℓ : ∀ i,0 < ℓ i) (A δ : ℝ) (z : RectanglePoint o ℓ) :
    H.rectangularValue F o ℓ hℓ A δ A z = p := by
  simp [rectangularValue]



end ControlledContraction
end
end AbelianTargets


