-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_linearCutCorrelation_eq_cutCorrelation
-- name    : Wikipedia.SzemeredisTheorem.linearCutCorrelation_eq_cutCorrelation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:55.903583+00:00
-- url     : https://prove2.me/theorems/63172e05-c8a5-4928-843c-968d5366a747
-- title:
--   Coordinate automorphisms transport linear cut correlations
-- statement:
--   Let $G$ be a finite additive commutative group, let $e_i$ be additive automorphisms indexed by $\mathrm{Fin}(r)$, and let $f,g$ be real functions and $u$ an arity-$r$ cut-test family. The weighted linear cut correlation determined by $e$ equals the ordinary cut correlation of $f,g$ against the pulled-back family $\operatorname{pullCutTest}(e,u)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutTransport.lean#L101-L127

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.linearCutCorrelation_eq_cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) :
    linearCutCorrelation r e f g u =
      cutCorrelation r f g (pullCutTest e u) := by sorry
