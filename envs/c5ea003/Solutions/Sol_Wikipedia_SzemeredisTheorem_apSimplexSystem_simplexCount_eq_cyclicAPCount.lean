-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexCount_eq_cyclicAPCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:44.263897+00:00
-- url     : https://prove2.me/submissions/4e4dc5af-3fc9-4c05-a260-c0c1581fd9be

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexSystem_simplexWeight

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators























/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

/-- A normalized average over a product is the corresponding iterated
normalized average. -/
theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

/-- Averaging a function that ignores a nonempty product coordinate does
not change its normalized average. -/
theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]



end Wikipedia.SzemeredisTheorem

end
/-!
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Exact normalized AP/simplex count correspondence.  The extra `r`
simplex coordinates form a uniform fiber over every pair `(a, d)`, so
normalization removes that fiber with no cardinality factor. -/
theorem solution
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by
  rw [WeightedSimplexSystem.simplexCount, cyclicAPCount]
  calc
    mean (apSimplexSystem (r + 2) N f).simplexWeight =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cyclicAPProduct (r + 2) N f
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact apSimplexSystem_simplexWeight (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cyclicAPProduct (r + 2) N f y.1.1 y.1.2) := by
      apply mean_equiv (simplexAPEquiv r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2) := by
      exact mean_prod_fst
        (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2)
    _ =
        mean₂ (fun a d =>
          cyclicAPProduct (r + 2) N f a d) := by
      exact mean_prod
        (fun a d => cyclicAPProduct (r + 2) N f a d)
