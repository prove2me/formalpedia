-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
-- name    : Wikipedia.SzemeredisTheorem.abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:37.186237+00:00
-- url     : https://prove2.me/theorems/ab355b42-17c8-4ef8-b6e9-099cc729e944
-- title:
--   Relative generalized bundle counting from an analytic step and envelope
-- statement:
--   Let the base-vertex type $J$ have decidable equality and the value type $G$ be finite and nonempty. Let real base weights $A$ on a finite base-edge family $H$ be idempotent and lie in $[0,1]$, with empty-edge weight $1$. Let the density function satisfy $p(\varnothing)=1$ and $p(e)\ge\alpha(|e|)$ for all $e\in H$. If the Tao bundle-counting step holds with bounds $\beta,\tau$ and $E$ is a valid envelope for $\alpha,\beta,\mu,\tau$, then every downward-closed bundle $B$ over a finite occurrence type with decidable equality satisfies $|\operatorname{count}_A(B)-\operatorname{main}_p(B)|\le E(\operatorname{order}B,|B.\mathrm{edges}|)\operatorname{main}_p(B)$. No decidable equality on $G$ is required.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean#L353-L977

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## The analytic one-edge interface -/
universe uJ uG
variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}
/-! ## Full double induction -/

omit [DecidableEq G] in

theorem Wikipedia.SzemeredisTheorem.abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
    [Nonempty G]
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hA01 :
      HypergraphBundle.BaseWeightsInUnitInterval H A)
    (_hAidempotent :
      HypergraphBundle.BaseWeightsIdempotent H A)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (hpLower :
      ∀ e ∈ H, α e.card ≤ p e)
    (hstep :
      HasTaoBundleCountingStep
        (H := H) A p β τ)
    (hE :
      IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount (B.pullbackBaseEdgeWeight A) -
        B.bundleMainProduct p| ≤
      E B.order B.edges.card *
        B.bundleMainProduct p := by sorry
