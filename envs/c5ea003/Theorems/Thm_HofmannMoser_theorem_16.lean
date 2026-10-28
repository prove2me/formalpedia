-- Prove2me | Theorems.Thm_HofmannMoser_theorem_16
-- name    : HofmannMoser.theorem_16
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-28T00:52:49.590983+00:00
-- url     : https://prove2.me/theorems/421b897d-d831-465c-ba35-e243ea968b95
-- title:
--   Theorem 16: Soundness of multivariate amortised resource analysis ($\Phi(\sigma, \Gamma : Q) - \Phi(v : Q') \ge m$)
-- statement:
--   This is Theorem 16 of Hofmann and Moser (TLCA 2015, p. 252), the main soundness theorem of multivariate amortised resource analysis for term rewrite systems.
--
--   Assume the standing conditions of Sections 2–4:
--   1. $S$ is a finite nonempty constructor signature (`FiniteConstructors C`), $(\mathcal{C}, \mathcal{D})$ is a finite overall signature with at least one constant (`FiniteSignature C D`), and $P$ is a representative policy (`RepPolicy C`).
--   2. $R$ is a finite (`FiniteSystem R`), syntactically orthogonal (`SyntacticallyOrthogonal R`), and completely defined (`CompletelyDefined R`) constructor term rewrite system.
--   3. $F$ (`AnnotatedSignatures C D`) consists of extensional counted and cost-free annotated signatures (`AnnotatedSignatureExtensional F.counted` and `AnnotatedSignatureExtensional F.costFree`) such that $R$ is bounded with respect to $F$ (`BoundedSignatures S P F R`).
--   4. $\Gamma = (x_1, \dots, x_n)$ (`xs : Fin n → Nat`) is a context of pairwise distinct variables (`Function.Injective xs`), $Q$ is a length-$n$ input annotation (`Annotation C n`), $t$ is a term (`Term C D`), $Q'$ is a length-$1$ output annotation (`Annotation C 1`), and $\Gamma : Q \vdash t : Q'$ is derivable in counted mode (`Typing S P F .counted n xs Q t Q'`).
--   5. $\sigma$ (`Substitution C D`) is a normalised substitution (`σ.Normalised`) such that every context variable $x_i$ lies in $\operatorname{dom}(\sigma)$ with $\sigma(x_i) = v_i$ (`(vs i).toTerm`) for ground constructor values $v_1, \dots, v_n$ (`vs : Fin n → Value C`).
--
--   If $t$ evaluates under $\sigma$ to a ground constructor value $v$ (`v.toTerm`) in $m \in \mathbb{N}$ innermost rewrite steps (`Evaluates R σ t m v.toTerm`), then the difference between the input potential and the output potential bounds the step count $m$:
--
--   $$\Phi(v_1, \dots, v_n : Q) - \Phi(v : Q') \ge m.$$
--
--   This theorem guarantees that any static resource bound derived in the type system of Figure 2 is a sound upper bound on the number of innermost evaluation steps on all ground constructor inputs.
-- source:
--   Hofmann--Moser 2015, Multivariate Amortised Resource Analysis for Term Rewrite Systems, TLCA 2015, https://doi.org/10.4230/LIPIcs.TLCA.2015.241, Section 4, p. 252, Theorem 16

import Definitions.Def_HofmannMoser_Syntax
import Definitions.Def_HofmannMoser_Potential
import Definitions.Def_HofmannMoser_Typing

universe u

namespace HofmannMoser

theorem theorem_16 {C D : Nat → Type u}
    (S : FiniteConstructors C) (P : RepPolicy C)
    (F : AnnotatedSignatures C D) (R : RewriteSystem C D)
    (hFinSig : FiniteSignature C D)
    (hFinSys : FiniteSystem R)
    (hOrth : SyntacticallyOrthogonal R)
    (hCompDef : CompletelyDefined R)
    (hExtCounted : AnnotatedSignatureExtensional F.counted)
    (hExtCostFree : AnnotatedSignatureExtensional F.costFree)
    (hBounded : BoundedSignatures S P F R)
    {n : Nat} (xs : Fin n → Nat) (hDistinct : Function.Injective xs)
    (Q : Annotation C n) (t : Term C D) (Q' : Annotation C 1)
    (hType : Typing S P F .counted n xs Q t Q')
    (σ : Substitution C D) (hNorm : σ.Normalised)
    (vs : Fin n → Value C)
    (hDom : ∀ i, xs i ∈ σ.dom)
    (hSubst : ∀ i, σ.assignment (xs i) = (vs i).toTerm)
    (m : Nat) (v : Value C)
    (hEval : Evaluates R σ t m v.toTerm) :
    potential Q vs - potential Q' (fun _ ↦ v) ≥ (m : Rat) := by sorry

end HofmannMoser
