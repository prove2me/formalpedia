-- Prove2me | Definitions.Def_EML_DepthCompression
-- name    : EML_DepthCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:14.356423+00:00
-- url     : https://prove2.me/theorems/04f3030c-d6f8-411d-a06b-a966184e2459
-- title:
--   Aether Catalog definitions — EML_DepthCompression
-- statement:
--   Definition bundle for the Aether Catalog module `EML.DepthCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/DepthCompression.lean by skeleton subtraction
import Mathlib

/-!
# Depth compression of exponential–logarithmic expressions

An **EML term** is a syntactic expression in one real variable built from the
variable, real constants, `+`, `*`, `Real.exp` and `Real.log`.  Its *depth* is
the height of its syntax tree.

The theme of this file is **depth compression**: the exponential–logarithmic
primitives collapse an unbounded amount of multiplicative structure into a
bounded amount of syntax.  Concretely:

* `Term.naivePow n` computes `y ↦ y ^ n` by iterated multiplication and has
  depth exactly `n` (for `n ≥ 1`), i.e. depth growing linearly in `n`
  (`Term.naivePow_depth`);
* `Term.monoExpLog n` computes the *same* function on the positive half-line
  through `y ↦ exp (n · log y)` and has depth `3`, independently of `n`
  (`Term.monoExpLog_eval`, `Term.monoExpLog_depth`);
* more generally `Term.rpowExpLog a` computes the real power `y ↦ y ^ a` for
  every real exponent `a`, again in depth `3` (`Term.rpowExpLog_eval`).

The separation is recorded in `depth_compression` and
`depth_compression_unbounded`: the naive family has unbounded depth while the
exp–log family computing the same functions is uniformly of depth `3`.

Basic structural facts (`Term.eval_add`, `Term.depth_mul`, …) and the fact that
depth-`0` terms are exactly the variable and the constants
(`Term.eval_of_depth_eq_zero`) round out the API.
-/

namespace EML.DepthCompression

/-- Syntax of exponential–logarithmic (EML) terms in one real variable. -/
inductive Term : Type
  | var : Term
  | const : ℝ → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | exp : Term → Term
  | log : Term → Term
  deriving Inhabited

namespace Term

/-- Interpretation of an EML term as a real function.  Outside its natural
domain the junk value `Real.log 0 = 0` is used. -/
noncomputable def eval : Term → ℝ → ℝ
  | var, y => y
  | const c, _ => c
  | add a b, y => eval a y + eval b y
  | mul a b, y => eval a y * eval b y
  | exp a, y => Real.exp (eval a y)
  | log a, y => Real.log (eval a y)

/-- The depth (syntax-tree height) of an EML term. -/
def depth : Term → ℕ
  | var => 0
  | const _ => 0
  | add a b => 1 + max (depth a) (depth b)
  | mul a b => 1 + max (depth a) (depth b)
  | exp a => 1 + depth a
  | log a => 1 + depth a




/-! ## The naive (iterated multiplication) representation of a monomial -/

/-- `naivePow n` is the term `y * (y * (⋯ * 1))` with `n` factors: the monomial
`y ^ n` written using multiplications only. -/
def naivePow : ℕ → Term
  | 0 => const 1
  | n + 1 => mul var (naivePow n)



/-! ## The exp–log (depth 3) representation -/

/-- `rpowExpLog a` is the depth-3 term `exp (a * log y)`, which computes the real
power `y ↦ y ^ a` on the positive half-line. -/
def rpowExpLog (a : ℝ) : Term := exp (mul (const a) (log var))

/-- `monoExpLog n` is the depth-3 term `exp (n * log y)` computing the monomial
`y ↦ y ^ n` on the positive half-line. -/
def monoExpLog (n : ℕ) : Term := rpowExpLog (n : ℝ)





end Term

/-! ## The compression theorem -/



end EML.DepthCompression


