-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
-- name    : ErdosProblems_Erdos251_PaperStreamingCertificateV5
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:47:35.30399+00:00
-- url     : https://prove2.me/theorems/61835c61-10ce-4be1-a249-09d88f48c2a4
-- title:
--   Prime-prefix state and block scanner
-- statement:
--   Defines the binary Horner accumulator $H_0=0$, $H_{n+1}=2H_n+p_n$, the prime-prefix state, and a scanner over finite integer intervals. At a prime $m$ the scanner increments the count and updates $A$ to $2A+m$; at other integers it leaves the pair unchanged. Separate theorems prove the prefix semantics and block-composition rule.
-- source:
--   Pinned Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/PaperStreamingCertificateV5.lean#L19-L21; https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/PaperStreamingCertificateV5.lean#L36-L37; https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/PaperStreamingCertificateV5.lean#L39-L41; https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/PaperStreamingCertificateV5.lean#L59-L63

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Restartable streaming prime certificate

Unlike primeSumLoop, the integer prefix is accumulated by Horner's rule:
A <- 2*A+p when a prime is encountered.  Fixed-size blocks can be compiled
separately and their endpoint equalities chained.  Generated endpoint
literals are not trusted: each block must succeed with `decide +kernel`.
Neither native_decide nor an external primality oracle is used.  Primality
is decided by `Fast.isPrimeG` (`GcdPrimality`), which equals the
trial-division test `isPrimeTD` and costs one gcd per scanned integer.
-/

open scoped BigOperators
open Finset
namespace ErdosProblems.Erdos251.PaperV5.Streaming

noncomputable def primeHorner : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * primeHorner n + prime0 n



def step (m : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if Fast.isPrimeG m then (s.1 + 1, 2 * s.2 + m) else s

def primePrefix : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 => step m (primePrefix m)




def scanBlock (start length : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  match length with
  | 0 => s
  | length + 1 => scanBlock (start + 1) length (step start s)
termination_by length







end ErdosProblems.Erdos251.PaperV5.Streaming


