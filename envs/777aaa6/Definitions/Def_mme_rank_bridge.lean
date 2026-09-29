-- Prove2me | Definitions.Def_mme_rank_bridge
-- name    : mme_rank_bridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:37:40.293422+00:00
-- url     : https://prove2.me/theorems/de297067-65a5-42fe-b6f8-533dc4eaf4fe
-- statement:
--   **Reconciling concrete and abstract tensor rank on the tensor quotient.**
--
--   This file bridges the *concrete* rank machinery defined directly on `TensorObj` (`tensorRankObj`, `tensorAsymptoticRank` from `Def_mme_tensor_rank`) with the *abstract* `StrassenPreorder.rank` / `StrassenPreorder.asymptoticRank` machinery instantiated on the tensor quotient `TensorQ K d` via its canonical preorder `tensorStrassen` (from `Def_mme_tensor_quotient`).
--
--   **Descent lemmas.** `toQ : TensorObj K d \to TensorQ K d` is a semiring homomorphism on the relevant combinators:
--   - `toQ_bigAdd` — $\mathrm{toQ}(\bigoplus_i X_i) = \sum_i \mathrm{toQ}(X_i)$.
--   - `toQ_kron` — $\mathrm{toQ}(X \otimes Y) = \mathrm{toQ}(X) \cdot \mathrm{toQ}(Y)$.
--   - `toQ_kronPow` — $\mathrm{toQ}(X^{\otimes n}) = \mathrm{toQ}(X)^n$.
--
--   **Rank reconciliation.**
--   - `rank_tensorStrassen_toQ` — $\mathrm{StrassenPreorder.rank}(\mathrm{tensorStrassen})(\mathrm{toQ}\,X) = \mathrm{tensorRankObj}\,X$. Both sides are an `sInf` over restrictions of $X$ by the diagonal $I_r$; the equality is by matching the witness sets pointwise.
--   - `tensorAsymptoticRank_eq` — same identification at the asymptotic level: $\mathrm{StrassenPreorder.asymptoticRank}(\mathrm{tensorStrassen})(\mathrm{toQ}\,X) = \mathrm{tensorAsymptoticRank}\,X$.
--
--   **Where used.** Reusable machinery for the tensor bridge file (`Def_mme_tensor_bridge`), particularly its `bridge_asymptoticRank`. Must NOT import `Def_mme_tensor_bridge` — the dependency goes one way.

import Definitions.Def_mme_strassen_preorder
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_flattening

/-! # Reconciling concrete and abstract tensor rank on the quotient (MME)

This file bridges the *concrete* rank machinery defined directly on `TensorObj`
(`tensorRankObj`, `tensorAsymptoticRank`) with the *abstract* Strassen-preorder rank
machinery (`StrassenPreorder.rank`, `StrassenPreorder.asymptoticRank`) instantiated on
the isomorphism quotient `TensorQ` via its own `tensorStrassen` instance.

The descent lemmas (`toQ_bigAdd`, `toQ_kron`, `toQ_kronPow`) say that `toQ` is a
semiring homomorphism on the relevant combinators, and the two key reconciliation
results (`rank_tensorStrassen_toQ`, `tensorAsymptoticRank_eq`) identify the concrete and
abstract ranks of `toQ X`.

This is the reusable machinery the tensor bridge file (`Def_mme_tensor_bridge`) consumes
for its `bridge_asymptoticRank`. It must NOT import that file (which imports this one). -/

universe u

open PiTensorProduct TensorProduct BigOperators

namespace MME

namespace TensorQ

variable {K : Type u} [Field K] {d : ℕ}

/-! ## `toQ` is a semiring homomorphism on the combinators

`add`/`mul` on `TensorQ` are descended from `TensorObj.add`/`kron`, so `toQ`
takes `bigAdd`/`kron`/`kronPow` to the corresponding `+`/`*`/`^`. -/

/-- The finite direct sum `bigAdd` descends to `∑` under `toQ`. -/
theorem toQ_bigAdd {k : ℕ} (f : Fin k → TensorObj K d) :
    toQ (TensorObj.bigAdd f) = ∑ i, toQ (f i) := by
  induction k with
  | zero =>
    -- `bigAdd` on the empty family is `zeroObj`, whose class is `0`.
    show toQ TensorObj.zeroObj = _
    rw [Fin.sum_univ_zero]; rfl
  | succ n ih =>
    match n, f with
    | 0, f =>
      -- `bigAdd` on a single object is the object itself.
      show toQ (f 0) = _
      rw [Fin.sum_univ_one]
    | (m+1), f =>
      show toQ (TensorObj.add (f 0) (TensorObj.bigAdd (fun i => f i.succ))) = _
      rw [Fin.sum_univ_succ (f := fun i => toQ (f i)), ← toQ_add, ih (fun i => f i.succ)]

/-- The Kronecker product descends to `*` under `toQ` (definitionally, `mul` on the
quotient is `kron` lifted). -/
theorem toQ_kron (X Y : TensorObj K d) :
    toQ (TensorObj.kron X Y) = toQ X * toQ Y := (toQ_mul X Y).symm

/-- The `n`-fold Kronecker power descends to `^` under `toQ`. -/
theorem toQ_kronPow (X : TensorObj K d) (n : ℕ) :
    toQ (TensorObj.kronPow X n) = (toQ X) ^ n := by
  induction n with
  | zero =>
    show toQ TensorObj.oneObj = _
    rw [pow_zero]; rfl
  | succ m ih =>
    show toQ (TensorObj.kron X (TensorObj.kronPow X m)) = _
    rw [toQ_kron, ih, pow_succ, mul_comm]

/-! ## The natural-number cast on the quotient is `toQ ∘ diagObj`

The `CommSemiring`'s `natCast` field is exactly `TensorQ.natCast`, so the `Nat.cast`
of `n` is the class of the diagonal object `diagObj K d n`. -/

/-- `(n : TensorQ K d) = toQ (diagObj K d n)`. -/
theorem natCast_eq (n : ℕ) : (n : TensorQ K d) = toQ (TensorObj.diagObj K d n) := rfl

/-! ## Rank reconciliation -/

/-- The abstract rank of `toQ X` (in the quotient's Strassen preorder) equals the
concrete tensor rank of `X`. The two `sInf`-sets coincide because
`(n : TensorQ) = toQ (diagObj n)` and `le (toQ X) (toQ (diagObj n)) ↔ Restrict X (diagObj n)`. -/
theorem rank_tensorStrassen_toQ (hd : 1 < d) (X : TensorObj K d) :
    StrassenPreorder.rank (tensorStrassen K d hd) (toQ X) = tensorRankObj X := by
  unfold StrassenPreorder.rank tensorRankObj
  -- the two defining `sInf`-sets coincide
  have hset : {n : ℕ | (tensorStrassen K d hd).le (toQ X) (n : TensorQ K d)}
      = {r : ℕ | TensorObj.Restrict X (TensorObj.diagObj K d r)} := by
    ext n
    -- `(tensorStrassen …).le (toQ X) (↑n) ↔ Restrict X (diagObj n)`
    show le (toQ X) (n : TensorQ K d) ↔ TensorObj.Restrict X (TensorObj.diagObj K d n)
    rw [natCast_eq]
    exact le_toQ X (TensorObj.diagObj K d n)
  rw [hset]

/-! ## Asymptotic-rank reconciliation -/

/-- The concrete asymptotic tensor rank of `X` equals the abstract asymptotic rank of
`toQ X` in the quotient's Strassen preorder. Both are
`⨅ n, (rank (X^⊗(n+1)))^(1/(n+1))`; combine the rank reconciliation with `toQ_kronPow`. -/
theorem tensorAsymptoticRank_eq (hd : 1 < d) (X : TensorObj K d) :
    tensorAsymptoticRank X =
      StrassenPreorder.asymptoticRank (tensorStrassen K d hd) (toQ X) := by
  unfold tensorAsymptoticRank StrassenPreorder.asymptoticRank
  refine iInf_congr (fun n => ?_)
  -- the exponents match; reduce to equality of the (cast) ranks
  congr 1
  -- `(tensorRankObj (kronPow X (n+1)) : ℝ) = (rank (tensorStrassen …) ((toQ X) ^ (n+1)) : ℝ)`
  rw [← rank_tensorStrassen_toQ hd (TensorObj.kronPow X (n + 1)), toQ_kronPow]

end TensorQ

end MME


